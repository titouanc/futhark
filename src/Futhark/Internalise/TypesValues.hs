{-# LANGUAGE FlexibleContexts #-}
module Futhark.Internalise.TypesValues
  (
   -- * Internalising types
    internaliseReturnType
  , internaliseEntryReturnType
  , internaliseParamTypes
  , internaliseType
  , internaliseUniqueness
  , internalisePrimType
  , internalisedTypeSize

  -- * Internalising values
  , internalisePrimValue
  , internaliseValue
  )
  where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Array as A
import Data.List
import qualified Data.Map.Strict as M
import Data.Monoid

import Prelude hiding (mapM)

import Language.Futhark as E
import Futhark.Representation.SOACS as I
import Futhark.Internalise.Monad
import Futhark.MonadFreshNames

internaliseUniqueness :: E.Uniqueness -> I.Uniqueness
internaliseUniqueness E.Nonunique = I.Nonunique
internaliseUniqueness E.Unique = I.Unique

internaliseParamTypes :: [E.TypeBase (E.ShapeDecl VName) als]
                      -> InternaliseM ([[I.TypeBase ExtShape Uniqueness]],
                                       M.Map VName Int)
internaliseParamTypes ts = do
  (ts', (_, subst, _)) <- runStateT (mapM internaliseDeclType' ts) (0, M.empty, mempty)
  return (ts', subst)

internaliseReturnType :: E.TypeBase (E.ShapeDecl VName) als
                      -> InternaliseM ([I.TypeBase ExtShape Uniqueness],
                                       M.Map VName Int,
                                       ConstParams)
internaliseReturnType t = do
  (ts', subst', cm') <- internaliseEntryReturnType t
  return (concat ts', subst', cm')

-- | As 'internaliseReturnType', but returns components of a top-level
-- tuple type piecemeal.
internaliseEntryReturnType :: E.TypeBase (E.ShapeDecl VName) als
                           -> InternaliseM ([[I.TypeBase ExtShape Uniqueness]],
                                            M.Map VName Int,
                                            ConstParams)
internaliseEntryReturnType t = do
  let ts = case isTupleRecord t of Just tts -> tts
                                   _        -> [t]
  (ts', (_, subst', cm')) <-
    runStateT (mapM internaliseDeclType' ts) (0, mempty, mempty)
  return (ts', subst', cm')

internaliseType :: E.ArrayShape shape =>
                   E.TypeBase shape als
                -> InternaliseM [I.TypeBase I.Rank Uniqueness]
internaliseType t = do
  (t', _) <- runStateT
             (internaliseDeclType' $ vacuousShapeAnnotations t)
             (0, M.empty, mempty)
  return $ map I.rankShaped t'

internaliseDeclType' :: E.TypeBase (E.ShapeDecl VName) als
                     -> StateT (Int, M.Map VName Int, ConstParams)
                        InternaliseM [I.TypeBase ExtShape Uniqueness]
internaliseDeclType' orig_t =
  case orig_t of
    E.Prim bt -> return [I.Prim $ internalisePrimType bt]
    E.TypeVar v -> do
      v' <- lift $ lookupSubst $ qualNameFromTypeName v
      mapM (extShaped . (`toDecl` Nonunique)) =<< lift (lookupTypeVar v')
    E.Record ets ->
      concat <$> mapM (internaliseDeclType' . snd) (sortFields ets)
    E.Array at ->
      internaliseArrayType at
  where internaliseArrayType (E.PrimArray bt shape u _) = do
          dims <- internaliseShape shape
          return [I.arrayOf (I.Prim $ internalisePrimType bt) (ExtShape dims) $
                  internaliseUniqueness u]

        internaliseArrayType (E.PolyArray v shape u _) = do
          ts <- lift $ lookupTypeVar =<< lookupSubst (qualNameFromTypeName v)
          dims <- internaliseShape shape
          forM ts $ \t -> do
            t' <- extShaped t
            return $ I.arrayOf t' (ExtShape dims) $ internaliseUniqueness u

        internaliseArrayType (E.RecordArray elemts shape u) = do
          innerdims <- ExtShape <$> internaliseShape shape
          ts <- concat <$> mapM (internaliseRecordArrayElem . snd) (sortFields elemts)
          return [ I.arrayOf ct innerdims $
                   if I.unique ct then Unique
                   else if I.primType ct then u
                        else I.uniqueness ct
                 | ct <- ts ]

        internaliseRecordArrayElem (PrimArrayElem bt _ _) =
          return [I.Prim $ internalisePrimType bt]
        internaliseRecordArrayElem (PolyArrayElem v _ _) = do
          v' <- lift $ lookupSubst $ qualNameFromTypeName v
          mapM (extShaped . (`toDecl` Nonunique)) =<< lift (lookupTypeVar v')
        internaliseRecordArrayElem (ArrayArrayElem aet) =
          internaliseArrayType aet
        internaliseRecordArrayElem (RecordArrayElem ts) =
          concat <$> mapM (internaliseRecordArrayElem . snd) (sortFields ts)

        newId = do (i,m,cm) <- get
                   put (i + 1, m, cm)
                   return i

        knownOrNewId name = do
          (i,m,cm) <- get
          case M.lookup name m of
            Nothing -> do put (i + 1, M.insert name i m, cm)
                          return i
            Just j  -> return j

        internaliseShape = mapM internaliseDim . E.shapeDims

        internaliseDim AnyDim =
          Ext <$> newId
        internaliseDim (ConstDim n) =
          Free <$> internaliseRDim (RConstDim n)
        internaliseDim (BoundDim name) =
          Ext <$> knownOrNewId name
        internaliseDim (NamedDim name) =
          Free <$> internaliseRDim (RNamedDim name)
        internaliseDim (ArithDim op l r) =
          Free <$> internaliseRDim (RArithDim op l r)

        internaliseRDim (RConstDim n) =
          return $ intConst I.Int32 $ toInteger n
        internaliseRDim (RNamedDim name) = do
          subst <- asks $ M.lookup (E.qualLeaf name) . envSubsts
          case subst of
            Just [v] -> return v
            _ -> do -- Then it must be a constant.
              let fname = nameFromString $ pretty name ++ "f"
              (i,m,cm) <- get
              case find ((==fname) . fst) cm of
                Just (_, known) -> return $ I.Var known
                Nothing -> do new <- lift $ newVName $ baseString $ qualLeaf name
                              put (i, m, (fname,new):cm)
                              return $ I.Var new
        internaliseRDim (RArithDim op l r) = do
          l' <- internaliseRDim l
          r' <- internaliseRDim r
          return $ I.BinExp op l' r'

        -- | Add vacuous existential type information to a type.  Every
        -- dimension will be its own 'Ext'.
        extShaped (I.Array et sz u) = do
          dims <- map I.Ext <$> replicateM (I.shapeRank sz) newId
          return $ I.Array et (I.ExtShape dims) u
        extShaped (I.Prim et) = return $ I.Prim et
        extShaped (I.Mem size space) = return $ I.Mem size space

internaliseSimpleType :: E.TypeBase E.Rank als
                      -> Maybe [I.TypeBase ExtShape NoUniqueness]
internaliseSimpleType = fmap (map I.fromDecl) . internaliseTypeWithUniqueness

internaliseTypeWithUniqueness :: E.TypeBase E.Rank als
                              -> Maybe [I.TypeBase ExtShape Uniqueness]
internaliseTypeWithUniqueness = flip evalStateT 0 . internaliseType'
  where internaliseType' E.TypeVar{} =
          lift Nothing
        internaliseType' (E.Prim bt) =
          return [I.Prim $ internalisePrimType bt]
        internaliseType' (E.Record ets) =
          concat <$> mapM (internaliseType' . snd) (sortFields ets)
        internaliseType' (E.Array at) =
          internaliseArrayType at

        internaliseArrayType E.PolyArray{} =
          lift Nothing
        internaliseArrayType (E.PrimArray bt shape u _) = do
          dims <- map Ext <$> replicateM (E.shapeRank shape) newId
          return [I.arrayOf (I.Prim $ internalisePrimType bt) (ExtShape dims) $
                  internaliseUniqueness u]
        internaliseArrayType (E.RecordArray elemts shape u) = do
          dims <- map Ext <$> replicateM (E.shapeRank shape) newId
          ts <- concat <$> mapM (internaliseRecordArrayElem . snd) (sortFields elemts)
          return [ I.arrayOf t (ExtShape dims) $
                    if I.unique t then Unique
                    else if I.primType t then u
                         else I.uniqueness t
                 | t <- ts ]

        internaliseRecordArrayElem PolyArrayElem{} =
          lift Nothing
        internaliseRecordArrayElem (PrimArrayElem bt _ _) =
          return [I.Prim $ internalisePrimType bt]
        internaliseRecordArrayElem (ArrayArrayElem at) =
          internaliseArrayType at
        internaliseRecordArrayElem (RecordArrayElem ts) =
          concat <$> mapM (internaliseRecordArrayElem . snd) (sortFields ts)

        newId = do i <- get
                   put $ i + 1
                   return i

-- | How many core language values are needed to represent one source
-- language value of the given type?
internalisedTypeSize :: E.ArrayShape shape =>
                        E.TypeBase shape als -> InternaliseM Int
internalisedTypeSize = fmap length . internaliseType

-- | Transform an external value to a number of internal values.
-- Roughly:
--
-- * The resulting list is empty if the original value is an empty
--   tuple.
--
-- * It contains a single element if the original value was a
-- singleton tuple or non-tuple.
--
-- * The list contains more than one element if the original value was
-- a non-empty non-singleton tuple.
--
-- Although note that the transformation from arrays-of-tuples to
-- tuples-of-arrays may also contribute to several discrete arrays
-- being returned for a single input array.
--
-- If the input value is or contains a non-regular array, 'Nothing'
-- will be returned.
internaliseValue :: E.Value -> Maybe [I.Value]
internaliseValue (E.ArrayValue arr rt) = do
  arrayvalues <- mapM internaliseValue $ A.elems arr
  ts <- internaliseSimpleType rt
  let arrayvalues' =
        case arrayvalues of
          [] -> replicate (length ts) []
          _  -> transpose arrayvalues
  zipWithM asarray ts arrayvalues'
  where asarray rt' values =
          let shape = determineShape (I.arrayRank rt') values
              values' = concatMap flat values
              size = product shape
          in if size == length values' then
               Just $ I.ArrayVal (A.listArray (0,size - 1) values')
               (I.elemType rt') shape
             else Nothing
        flat (I.PrimVal bv)      = [bv]
        flat (I.ArrayVal bvs _ _) = A.elems bvs
internaliseValue (E.PrimValue bv) =
  return [I.PrimVal $ internalisePrimValue bv]

determineShape :: Int -> [I.Value] -> [Int]
determineShape _ vs@(I.ArrayVal _ _ shape : _) =
  length vs : shape
determineShape r vs =
  length vs : replicate r 0

-- | Convert an external primitive to an internal primitive.
internalisePrimType :: E.PrimType -> I.PrimType
internalisePrimType (E.Signed t) = I.IntType t
internalisePrimType (E.Unsigned t) = I.IntType t
internalisePrimType (E.FloatType t) = I.FloatType t
internalisePrimType E.Bool = I.Bool

-- | Convert an external primitive value to an internal primitive value.
internalisePrimValue :: E.PrimValue -> I.PrimValue
internalisePrimValue (E.SignedValue v) = I.IntValue v
internalisePrimValue (E.UnsignedValue v) = I.IntValue v
internalisePrimValue (E.FloatValue v) = I.FloatValue v
internalisePrimValue (E.BoolValue b) = I.BoolValue b
