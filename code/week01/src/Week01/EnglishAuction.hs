-- language pragmas https://wiki.haskell.org/Language_Pragmas
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

{-
module definition and exports
https://www.haskell.org/tutorial/modules.html
-}
module Week01.EnglishAuction
    ( Auction (..)
    , StartParams (..), BidParams (..), CloseParams (..)
    , AuctionSchema
    , start, bid, close
    , endpoints
    , schemas
    , ensureKnownCurrencies
    , printJson
    , printSchemas
    , registeredKnownCurrencies
    , stage
    ) where

{- a list of imports -}
import           Control.Monad        hiding (fmap)
import           Data.Aeson           (ToJSON, FromJSON)
import           Data.List.NonEmpty   (NonEmpty (..))
import           Data.Map             as Map
import           Data.Text            (pack, Text)
import           GHC.Generics         (Generic)
import           Plutus.Contract      hiding (when)
import qualified PlutusTx             as PlutusTx
import           PlutusTx.Prelude     hiding (Semigroup(..), unless)
import qualified PlutusTx.Prelude     as Plutus
import           Ledger               hiding (singleton)
import           Ledger.Constraints   as Constraints
import qualified Ledger.Scripts       as Scripts
import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Value         as Value
import           Ledger.Ada           as Ada
import           Playground.Contract  (ensureKnownCurrencies, printSchemas, stage, printJson)
import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Prelude              (Semigroup (..))
import           Schema               (ToSchema)
import           Text.Printf          (printf)

-- data type to represent an auction, don't understand what Generic & ToSchema means
data Auction = Auction
    { aSeller   :: !PubKeyHash
    , aDeadline :: !Slot
    , aMinBid   :: !Integer
    , aCurrency :: !CurrencySymbol
    , aToken    :: !TokenName
    } deriving (Show, Generic, ToJSON, FromJSON, ToSchema)

-- define what does it mean for two auctions to be equal
instance Eq Auction where
    {-# INLINABLE (==) #-}
    a == b = (aSeller   a == aSeller   b) &&
             (aDeadline a == aDeadline b) &&
             (aMinBid   a == aMinBid   b) &&
             (aCurrency a == aCurrency b) &&
             (aToken    a == aToken    b)

-- don't know
PlutusTx.unstableMakeIsData ''Auction
PlutusTx.makeLift ''Auction

-- bid data type
data Bid = Bid
    { bBidder :: !PubKeyHash
    , bBid    :: !Integer
    } deriving Show

-- ...again
instance Eq Bid where
    {-# INLINABLE (==) #-}
    b == c = (bBidder b == bBidder c) &&
             (bBid    b == bBid    c)

PlutusTx.unstableMakeIsData ''Bid
PlutusTx.makeLift ''Bid

-- another data type, describing redeemer
data AuctionAction = MkBid Bid | Close
    deriving Show

PlutusTx.unstableMakeIsData ''AuctionAction
PlutusTx.makeLift ''AuctionAction

-- the way to represent running auction, describing datum
data AuctionDatum = AuctionDatum
    { adAuction    :: !Auction
    , adHighestBid :: !(Maybe Bid)
    } deriving Show

PlutusTx.unstableMakeIsData ''AuctionDatum
PlutusTx.makeLift ''AuctionDatum

-- describing the contract I suppose
data Auctioning
instance Scripts.ScriptType Auctioning where
    type instance RedeemerType Auctioning = AuctionAction
    type instance DatumType Auctioning = AuctionDatum

-- returns the minBid for a current datum
{-# INLINABLE minBid #-}
minBid :: AuctionDatum -> Integer
minBid AuctionDatum{..} = case adHighestBid of
    Nothing      -> aMinBid adAuction
    Just Bid{..} -> bBid + 1

{- old definition of context might be helpul
https://github.com/input-output-hk/plutus/blob/a1fc45ea68a45f23e9770f13b2643e1a87dd3c6f/plutus-ledger-api/src/Plutus/V1/Ledger/Contexts.hs
-}
{-# INLINABLE mkAuctionValidator #-}
mkAuctionValidator :: AuctionDatum -> AuctionAction -> ValidatorCtx -> Bool
mkAuctionValidator ad redeemer ctx =
    traceIfFalse "wrong input value" correctInputValue &&
    case redeemer of
        MkBid b@Bid{..} ->
            -- the bid is not too low
            traceIfFalse "bid too low"        (sufficientBid bBid)         &&
            traceIfFalse "wrong output datum" (correctBidOutputDatum b)    &&
            traceIfFalse "wrong output value" (correctBidOutputValue bBid) &&
            traceIfFalse "wrong refund"       correctBidRefund             &&
            traceIfFalse "too late"           correctBidSlotRange
        Close           ->
            traceIfFalse "too early" correctCloseSlotRange &&
            case adHighestBid ad of
                Nothing      ->
                    traceIfFalse "expected seller to get token" (getsValue (aSeller auction) tokenValue)
                Just Bid{..} ->
                    traceIfFalse "expected highest bidder to get token" (getsValue bBidder tokenValue) &&
                    traceIfFalse "expected seller to get highest bid" (getsValue (aSeller auction) $ Ada.lovelaceValueOf bBid)

  where
    -- information about transaction
    info :: TxInfo
    info = valCtxTxInfo ctx

    -- 
    input :: TxInInfo
    input =
      let
        -- CHECK
        {- checking that transaction input was verified https://github.com/input-output-hk/plutus/blob/a1fc45ea68a45f23e9770f13b2643e1a87dd3c6f/plutus-ledger-api/src/Plutus/V1/Ledger/Contexts.hs#L90
        -}
        isScriptInput i = case txInInfoWitness i of
            Nothing -> False
            Just _  -> True
        -- compose a list of all transactions which has been verified
        xs = [i | i <- txInfoInputs info, isScriptInput i]
      in
        -- select only one input from a transaction, should have only one anyway...
        case xs of
            [i] -> i
            _   -> traceError "expected exactly one script input"

    -- Value consumed by this txn input
    -- https://github.com/input-output-hk/plutus/blob/a1fc45ea68a45f23e9770f13b2643e1a87dd3c6f/plutus-ledger-api/src/Plutus/V1/Ledger/Contexts.hs#L92
    inVal :: Value
    inVal = txInInfoValue input

    -- an auction description from datum
    auction :: Auction
    auction = adAuction ad

    -- value for 1 token
    -- https://github.com/input-output-hk/plutus/blob/a1fc45ea68a45f23e9770f13b2643e1a87dd3c6f/plutus-ledger-api/src/Plutus/V1/Ledger/Value.hs#L264
    -- create a value of a currency
    -- | Make a 'Value' containing only the given quantity of the given currency.
    tokenValue :: Value
    tokenValue = Value.singleton (aCurrency auction) (aToken auction) 1

    -- CHECK, why do we compare inVal with tokenValue if there were no prior bidders?
    correctInputValue :: Bool
    correctInputValue = inVal == case adHighestBid ad of
        Nothing      -> tokenValue
        -- OK, value of bid, I think
        Just Bid{..} -> tokenValue Plutus.<> Ada.lovelaceValueOf bBid

    sufficientBid :: Integer -> Bool
    sufficientBid amount = amount >= minBid ad

    ownOutput   :: TxOutInfo
    outputDatum :: AuctionDatum
    -- https://github.com/input-output-hk/plutus/blob/a1fc45ea68a45f23e9770f13b2643e1a87dd3c6f/plutus-ledger-api/src/Plutus/V1/Ledger/Contexts.hs#L154
    -- don't understand the predicate in plutus code
    (ownOutput, outputDatum) = case getContinuingOutputs ctx of
        [o] -> case txOutType o of
            -- CHECK, what about refund when the wallet is outbid?
            PayToPubKey   -> traceError "wrong output type"
            -- https://github.com/input-output-hk/plutus/blob/a1fc45ea68a45f23e9770f13b2643e1a87dd3c6f/plutus-ledger-api/src/Plutus/V1/Ledger/Tx.hs#L326
            PayToScript h -> case findDatum h info of
                Nothing        -> traceError "datum not found"
                Just (Datum d) ->  case PlutusTx.fromData d of
                    Just ad' -> (o, ad')
                    Nothing  -> traceError "error decoding data"
        _   -> traceError "expected exactly one continuing output"

    -- auction is still the same and the bid we did is the highest one
    correctBidOutputDatum :: Bid -> Bool
    correctBidOutputDatum b = (adAuction outputDatum == auction)   &&
                              (adHighestBid outputDatum == Just b)
    
    -- out value is the same as bidding amount for some reason
    -- https://github.com/input-output-hk/plutus/blob/a1fc45ea68a45f23e9770f13b2643e1a87dd3c6f/plutus-ledger-api/src/Plutus/V1/Ledger/Tx.hs#L344
    correctBidOutputValue :: Integer -> Bool
    correctBidOutputValue amount =
        txOutValue ownOutput == tokenValue Plutus.<> Ada.lovelaceValueOf amount

    -- CHECK, why do we always compare with bBid, I don't get it
    correctBidRefund :: Bool
    correctBidRefund = case adHighestBid ad of
        Nothing      -> True
        Just Bid{..} ->
          let
            os = [ o
                 | o <- txInfoOutputs info
                 , txOutAddress o == PubKeyAddress bBidder
                 ]
          in
            case os of
                [o] -> txOutValue o == Ada.lovelaceValueOf bBid
                _   -> traceError "expected exactly one refund output"

    -- OK
    correctBidSlotRange :: Bool
    correctBidSlotRange = to (aDeadline auction) `contains` txInfoValidRange info

    -- OK
    correctCloseSlotRange :: Bool
    correctCloseSlotRange = from (aDeadline auction) `contains` txInfoValidRange info

    -- checks that outputs contain a certain value for a specific address
    getsValue :: PubKeyHash -> Value -> Bool
    getsValue h v =
      let
        [o] = [ o'
              | o' <- txInfoOutputs info
              , txOutValue o' == v
              ]
      in
        txOutAddress o == PubKeyAddress h

-- boilerplate
auctionInstance :: Scripts.ScriptInstance Auctioning
auctionInstance = Scripts.validator @Auctioning
    $$(PlutusTx.compile [|| mkAuctionValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @AuctionDatum @AuctionAction

auctionValidator :: Validator
auctionValidator = Scripts.validatorScript auctionInstance

-- CHECK, why do we need a hash?
auctionHash :: Ledger.ValidatorHash
auctionHash = Scripts.validatorHash auctionValidator

auctionAddress :: Ledger.Address
auctionAddress = ScriptAddress auctionHash

-- define interface, forms
data StartParams = StartParams
    { spDeadline :: !Slot
    , spMinBid   :: !Integer
    , spCurrency :: !CurrencySymbol
    , spToken    :: !TokenName
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

data BidParams = BidParams
    { bpCurrency :: !CurrencySymbol
    , bpToken    :: !TokenName
    , bpBid      :: !Integer
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

data CloseParams = CloseParams
    { cpCurrency :: !CurrencySymbol
    , cpToken    :: !TokenName
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

-- define interface, buttons
type AuctionSchema =
    BlockchainActions
        .\/ Endpoint "start" StartParams
        .\/ Endpoint "bid"   BidParams
        .\/ Endpoint "close" CloseParams

start :: (HasBlockchainActions s, AsContractError e) => StartParams -> Contract w s e ()
start StartParams{..} = do
    pkh <- pubKeyHash <$> ownPubKey
    let a = Auction
                { aSeller   = pkh
                , aDeadline = spDeadline
                , aMinBid   = spMinBid
                , aCurrency = spCurrency
                , aToken    = spToken
                }
        d = AuctionDatum
                { adAuction    = a
                , adHighestBid = Nothing
                }
        v = Value.singleton spCurrency spToken 1
        -- create some sort of constraints
        tx = mustPayToTheScript d v
    -- CHECK, bind auction with these contraints?
    ledgerTx <- submitTxConstraints auctionInstance tx
    -- CHECK, listen for confirmation?
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ printf "started auction %s for token %s" (show a) (show v)

bid :: forall w s. HasBlockchainActions s => BidParams -> Contract w s Text ()
bid BidParams{..} = do
    (oref, o, d@AuctionDatum{..}) <- findAuction bpCurrency bpToken
    logInfo @String $ printf "found auction utxo with datum %s" (show d)
    -- could be done offchain or not?
    when (bpBid < minBid d) $
        throwError $ pack $ printf "bid lower than minimal bid %d" (minBid d)
    pkh <- pubKeyHash <$> ownPubKey
    let b  = Bid {bBidder = pkh, bBid = bpBid}
        -- create new datuum
        d' = d {adHighestBid = Just b}
        v  = Value.singleton bpCurrency bpToken 1 <> Ada.lovelaceValueOf bpBid
        r  = Redeemer $ PlutusTx.toData $ MkBid b

        -- CHECK, don't understand, boilerplate?
        lookups = Constraints.scriptInstanceLookups auctionInstance <>
                  Constraints.otherScript auctionValidator          <>
                  Constraints.unspentOutputs (Map.singleton oref o)
        tx      = case adHighestBid of
                    Nothing      -> mustPayToTheScript d' v                            <>
                                    mustValidateIn (to $ aDeadline adAuction)          <>
                                    mustSpendScriptOutput oref r
                    Just Bid{..} -> mustPayToTheScript d' v                            <>
                                    -- OK, refund
                                    mustPayToPubKey bBidder (Ada.lovelaceValueOf bBid) <>
                                    mustValidateIn (to $ aDeadline adAuction)          <>
                                    mustSpendScriptOutput oref r
    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ printf "made bid of %d lovelace in auction %s for token (%s, %s)"
        bpBid
        (show adAuction)
        (show bpCurrency)
        (show bpToken)

-- very similar to previous one
close :: forall w s. HasBlockchainActions s => CloseParams -> Contract w s Text ()
close CloseParams{..} = do
    (oref, o, d@AuctionDatum{..}) <- findAuction cpCurrency cpToken
    logInfo @String $ printf "found auction utxo with datum %s" (show d)

    let t      = Value.singleton cpCurrency cpToken 1
        r      = Redeemer $ PlutusTx.toData Close
        seller = aSeller adAuction

        lookups = Constraints.scriptInstanceLookups auctionInstance <>
                  Constraints.otherScript auctionValidator          <>
                  Constraints.unspentOutputs (Map.singleton oref o)
        tx      = case adHighestBid of
                    Nothing      -> mustPayToPubKey seller t                          <>
                                    mustValidateIn (from $ aDeadline adAuction)       <>
                                    mustSpendScriptOutput oref r
                    -- pay token to bidder, pay ada to seller, makes sense
                    Just Bid{..} -> mustPayToPubKey bBidder t                         <>
                                    mustPayToPubKey seller (Ada.lovelaceValueOf bBid) <>
                                    mustValidateIn (from $ aDeadline adAuction)       <>
                                    mustSpendScriptOutput oref r
    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ printf "closed auction %s for token (%s, %s)"
        (show adAuction)
        (show cpCurrency)
        (show cpToken)

-- do together, hard
findAuction :: HasBlockchainActions s
            => CurrencySymbol
            -> TokenName
            -> Contract w s Text (TxOutRef, TxOutTx, AuctionDatum)
findAuction cs tn = do
    utxos <- utxoAt $ ScriptAddress auctionHash
    let xs = [ (oref, o)
             | (oref, o) <- Map.toList utxos
             , Value.valueOf (txOutValue $ txOutTxOut o) cs tn == 1
             ]
    case xs of
        [(oref, o)] -> case txOutType $ txOutTxOut o of
            PayToPubKey   -> throwError "unexpected out type"
            PayToScript h -> case Map.lookup h $ txData $ txOutTxTx o of
                Nothing        -> throwError "datum not found"
                Just (Datum e) -> case PlutusTx.fromData e of
                    Nothing -> throwError "datum has wrong type"
                    Just d@AuctionDatum{..}
                        | aCurrency adAuction == cs && aToken adAuction == tn -> return (oref, o, d)
                        | otherwise                                           -> throwError "auction token missmatch"
        _           -> throwError "auction utxo not found"

-- boilerplate
endpoints :: Contract () AuctionSchema Text ()
endpoints = (start' `select` bid' `select` close') >> endpoints
  where
    start' = endpoint @"start" >>= start
    bid'   = endpoint @"bid"   >>= bid
    close' = endpoint @"close" >>= close

mkSchemaDefinitions ''AuctionSchema

myToken :: KnownCurrency
-- f = 66 https://youtu.be/IEn6jUo-0vU?t=2035
myToken = KnownCurrency (ValidatorHash "f") "Token" (TokenName "T" :| [])

mkKnownCurrencies ['myToken]
