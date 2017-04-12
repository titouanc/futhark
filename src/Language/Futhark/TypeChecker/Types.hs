{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Futhark.TypeChecker.Types
  ( checkTypeExp
  , ImplicitlyBound
  , implicitNameMap

  , unifyTypes

  , checkPattern
  , checkPatternGroup
  , InferredType(..)
  )
where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Loc
import Data.Maybe
import Data.Monoid
import qualified Data.Map.Strict as M

import Language.Futhark
import Language.Futhark.TypeChecker.Monad


-- | @t1 `unifyTypes` t2@ attempts to unify @t1@ and @t2@.  If
-- unification cannot happen, 'Nothing' is returned, otherwise a type
-- that combines the aliasing of @t1@ and @t2@ is returned.  The
-- uniqueness of the resulting type will be the least of the
-- uniqueness of @t1@ and @t2@.
unifyTypes :: (Monoid als, ArrayShape shape) =>
              TypeBase shape als
           -> TypeBase shape als
           -> Maybe (TypeBase shape als)
unifyTypes (Prim t1) (Prim t2)
  | t1 == t2  = Just $ Prim t1
  | otherwise = Nothing
unifyTypes (TypeVar t1) (TypeVar t2)
  | t1 == t2  = Just $ TypeVar t1
  | otherwise = Nothing
unifyTypes (Array at1) (Array at2) =
  Array <$> unifyArrayTypes at1 at2
unifyTypes (Record ts1) (Record ts2)
  | length ts1 == length ts2,
    sort (M.keys ts1) == sort (M.keys ts2) =
      Record <$> traverse (uncurry unifyTypes)
      (M.intersectionWith (,) ts1 ts2)
unifyTypes _ _ = Nothing

unifyArrayTypes :: (Monoid als, ArrayShape shape) =>
                   ArrayTypeBase shape als
                -> ArrayTypeBase shape als
                -> Maybe (ArrayTypeBase shape als)
unifyArrayTypes (PrimArray bt1 shape1 u1 als1) (PrimArray bt2 shape2 u2 als2)
  | Just shape <- unifyShapes shape1 shape2, bt1 == bt2 =
    Just $ PrimArray bt1 shape (u1 <> u2) (als1 <> als2)
unifyArrayTypes (PolyArray bt1 shape1 u1 als1) (PolyArray bt2 shape2 u2 als2)
  | Just shape <- unifyShapes shape1 shape2, bt1 == bt2 =
    Just $ PolyArray bt1 shape (u1 <> u2) (als1 <> als2)
unifyArrayTypes (RecordArray et1 shape1 u1) (RecordArray et2 shape2 u2)
  | Just shape <- unifyShapes shape1 shape2,
    sort (M.keys et1) == sort (M.keys et2) =
    RecordArray <$>
    traverse (uncurry unifyRecordArrayElemTypes) (M.intersectionWith (,) et1 et2) <*>
    pure shape <*> pure (u1 <> u2)
unifyArrayTypes _ _ =
  Nothing

unifyRecordArrayElemTypes :: (Monoid als, ArrayShape shape) =>
                             RecordArrayElemTypeBase shape als
                          -> RecordArrayElemTypeBase shape als
                          -> Maybe (RecordArrayElemTypeBase shape als)
unifyRecordArrayElemTypes (PrimArrayElem bt1 als1 u1) (PrimArrayElem bt2 als2 u2)
  | bt1 == bt2 = Just $ PrimArrayElem bt1 (als1 <> als2) (u1 <> u2)
  | otherwise  = Nothing
unifyRecordArrayElemTypes (PolyArrayElem bt1 als1 u1) (PolyArrayElem bt2 als2 u2)
  | bt1 == bt2 = Just $ PolyArrayElem bt1 (als1 <> als2) (u1 <> u2)
  | otherwise  = Nothing
unifyRecordArrayElemTypes (ArrayArrayElem at1) (ArrayArrayElem at2) =
  ArrayArrayElem <$> unifyArrayTypes at1 at2
unifyRecordArrayElemTypes (RecordArrayElem ts1) (RecordArrayElem ts2)
  | sort (M.keys ts1) == sort (M.keys ts2) =
    RecordArrayElem <$>
    traverse (uncurry unifyRecordArrayElemTypes) (M.intersectionWith (,) ts1 ts2)
unifyRecordArrayElemTypes _ _ =
  Nothing

data Bindage = BoundAsDim | BoundAsVar | UsedFree
             deriving (Show, Eq)

-- | The variables implicitly bound inside a pattern group (which can
-- include several types).
newtype ImplicitlyBound = ImplicitlyBound (M.Map (Namespace, Name) (VName, Bindage, SrcLoc))
                        deriving (Show)

instance Monoid ImplicitlyBound where
  mempty = ImplicitlyBound mempty
  ImplicitlyBound x `mappend` ImplicitlyBound y = ImplicitlyBound (x <> y)

implicitNameMap :: ImplicitlyBound -> NameMap
implicitNameMap (ImplicitlyBound m) = M.mapMaybe firstOne m
  where firstOne (x, BoundAsDim, _) = Just x
        firstOne (x, BoundAsVar, _) = Just x
        firstOne (_, UsedFree, _) = Nothing

checkTypeExp :: MonadTypeChecker m =>
                TypeExp Name
             -> m (TypeExp VName, StructType, ImplicitlyBound)
checkTypeExp te = do
  implicit <- checkForDuplicateNamesTypeExp mempty te
  bindNameMap (implicitNameMap implicit) $ do
    ((te', st), implicit') <- runStateT (checkTypeExp' te) implicit
    return (te', st, implicit')

checkTypeExp' :: MonadTypeChecker m =>
                 TypeExp Name
              -> StateT ImplicitlyBound m (TypeExp VName, StructType)
checkTypeExp' (TEVar name loc) = do
  (name', t) <- lift $ lookupType loc name
  return (TEVar name' loc, t)
checkTypeExp' (TETuple ts loc) = do
  (ts', ts_s) <- unzip <$> mapM checkTypeExp' ts
  return (TETuple ts' loc, tupleRecord ts_s)
checkTypeExp' t@(TERecord fs loc) = do
  -- Check for duplicate field names.
  let field_names = map fst fs
  unless (sort field_names == sort (nub field_names)) $
    throwError $ TypeError loc $ "Duplicate record fields in " ++ pretty t

  fs_and_ts <- traverse checkTypeExp' $ M.fromList fs
  let fs' = fmap fst fs_and_ts
      ts_s = fmap snd fs_and_ts
  return (TERecord (M.toList fs') loc, Record ts_s)
checkTypeExp' (TEArray t d loc) = do
  (t', st) <- checkTypeExp' t
  d' <- checkDimDecl d
  return (TEArray t' d' loc, arrayOf st (ShapeDecl [d']) Nonunique)
  where checkDimDecl AnyDim =
          return AnyDim
        checkDimDecl (ConstDim k) =
          return $ ConstDim k
        checkDimDecl (BoundDim v) =
          BoundDim <$> checkBoundDim loc v
        checkDimDecl (NamedDim v) =
          NamedDim <$> checkNamedDim loc v
        checkDimDecl (ArithDim op l r) = do
          l' <- checkRDimDecl l
          r' <- checkRDimDecl r
          return $ ArithDim op l' r'

        checkRDimDecl (RConstDim k) =
          return $ RConstDim k
        checkRDimDecl (RNamedDim v) =
          RNamedDim <$> checkNamedDim loc v
        checkRDimDecl (RArithDim op l r) = do
          l' <- checkRDimDecl l
          r' <- checkRDimDecl r
          return $ RArithDim op l' r'

checkTypeExp' (TEUnique t loc) = do
  (t', st) <- checkTypeExp' t
  case st of
    Array{} -> return (t', st `setUniqueness` Unique)
    _       -> throwError $ InvalidUniqueness loc $ toStructural st

checkNamedDim :: MonadTypeChecker m =>
                 SrcLoc -> QualName Name -> StateT ImplicitlyBound m (QualName VName)
checkNamedDim loc v = do
  (v', t) <- lift $ lookupVar loc v
  case t of
    Prim (Signed Int32) -> return v'
    _                   -> throwError $ DimensionNotInteger loc v

checkBoundDim :: MonadTypeChecker m =>
                 SrcLoc -> Name -> StateT ImplicitlyBound m VName
checkBoundDim loc v = lift $ checkName Term v loc

data InferredType = NoneInferred
                  | Inferred Type
                  | Ascribed (TypeBase (ShapeDecl VName) (Names VName))

checkPatternGroup :: MonadTypeChecker m =>
                     [(PatternBase NoInfo Name, InferredType)]
                  -> ([Pattern] -> m a)
                  -> m a
checkPatternGroup ps m = do
  implicit <- checkForDuplicateNames $ map fst ps
  bindNameMap (implicitNameMap implicit) $ do
    ps' <- evalStateT (mapM (uncurry checkPattern') ps) implicit
    m ps'

checkPattern :: MonadTypeChecker m =>
                PatternBase NoInfo Name -> InferredType
             -> (Pattern -> m a)
             -> m a
checkPattern p t m = do
  implicit <- checkForDuplicateNames [p]
  bindNameMap (implicitNameMap implicit) $ do
    p' <- evalStateT (checkPattern' p t) implicit
    m p'

checkPattern' :: MonadTypeChecker m =>
                 PatternBase NoInfo Name -> InferredType
              -> StateT ImplicitlyBound m Pattern

checkPattern' (PatternParens p loc) t =
  PatternParens <$> checkPattern' p t <*> pure loc

checkPattern' (Id (Ident name NoInfo loc)) (Inferred t) = do
  name' <- lift $ checkName Term name loc
  let t' = typeOf $ Var (qualName name') (Info t) loc
  return $ Id $ Ident name' (Info $ t' `setUniqueness` Nonunique) loc
checkPattern' (Id (Ident name NoInfo loc)) (Ascribed t) = do
  name' <- lift $ checkName Term name loc
  let t' = typeOf $ Var (qualName name') (Info $ removeShapeAnnotations t) loc
  return $ Id $ Ident name' (Info t') loc

checkPattern' (Wildcard _ loc) (Inferred t) =
  return $ Wildcard (Info $ t `setUniqueness` Nonunique) loc
checkPattern' (Wildcard _ loc) (Ascribed t) =
  return $ Wildcard (Info $ removeShapeAnnotations $ t `setUniqueness` Nonunique) loc

checkPattern' (TuplePattern ps loc) (Inferred t)
  | Just ts <- isTupleRecord t, length ts == length ps =
  TuplePattern <$> zipWithM checkPattern' ps (map Inferred ts) <*> pure loc
checkPattern' (TuplePattern ps loc) (Ascribed t)
  | Just ts <- isTupleRecord t, length ts == length ps =
      TuplePattern <$> zipWithM checkPattern' ps (map Ascribed ts) <*> pure loc
checkPattern' p@TuplePattern{} (Inferred t) =
  throwError $ TypeError (srclocOf p) $ "Pattern " ++ pretty p ++ " cannot match " ++ pretty t
checkPattern' p@TuplePattern{} (Ascribed t) =
  throwError $ TypeError (srclocOf p) $ "Pattern " ++ pretty p ++ " cannot match " ++ pretty t
checkPattern' (TuplePattern ps loc) NoneInferred =
  TuplePattern <$> mapM (`checkPattern'` NoneInferred) ps <*> pure loc

checkPattern' (RecordPattern p_fs loc) (Inferred (Record t_fs))
  | sort (map fst p_fs) == sort (M.keys t_fs) =
    RecordPattern . M.toList <$> check <*> pure loc
    where check = traverse (uncurry checkPattern') $ M.intersectionWith (,)
                  (M.fromList p_fs) (fmap Inferred t_fs)
checkPattern' (RecordPattern p_fs loc) (Ascribed (Record t_fs))
  | sort (map fst p_fs) == sort (M.keys t_fs) =
    RecordPattern . M.toList <$> check <*> pure loc
    where check = traverse (uncurry checkPattern') $ M.intersectionWith (,)
                  (M.fromList p_fs) (fmap Ascribed t_fs)
checkPattern' p@RecordPattern{} (Inferred t) =
  throwError $ TypeError (srclocOf p) $ "Pattern " ++ pretty p ++ " cannot match " ++ pretty t
checkPattern' p@RecordPattern{} (Ascribed t) =
  throwError $ TypeError (srclocOf p) $ "Pattern " ++ pretty p ++ " cannot match " ++ pretty t
checkPattern' (RecordPattern fs loc) NoneInferred =
  RecordPattern . M.toList <$> traverse (`checkPattern'` NoneInferred) (M.fromList fs) <*> pure loc

checkPattern' fullp@(PatternAscription p (TypeDecl t NoInfo)) maybe_outer_t = do
  (t', st) <- checkTypeExp' t
  let maybe_outer_t' = case maybe_outer_t of
                         Inferred outer_t -> Just $ vacuousShapeAnnotations outer_t
                         Ascribed outer_t -> Just outer_t
                         NoneInferred -> Nothing
      st' = fromStruct st
  case maybe_outer_t' of
    Just outer_t
      | Just t'' <- unifyTypes outer_t st' ->
          PatternAscription <$> checkPattern' p (Ascribed t'') <*>
          pure (TypeDecl t' (Info st))
      | otherwise ->
          let outer_t_for_error =
                modifyShapeAnnotations (fmap baseName) $ outer_t `setAliases` ()
          in throwError $ InvalidPatternError fullp outer_t_for_error Nothing $ srclocOf p
    _ -> PatternAscription <$> checkPattern' p (Ascribed st') <*>
         pure (TypeDecl t' (Info st))

checkPattern' p NoneInferred =
  throwError $ TypeError (srclocOf p) $ "Cannot determine type of " ++ pretty p

-- | Check for duplication of names inside a pattern group.
-- Duplication of bound shape names are permitted, but only if they
-- are not also bound as values.  Also, a bound size must not also be
-- used as free.
checkForDuplicateNames :: MonadTypeChecker m =>
                          [PatternBase NoInfo Name] -> m ImplicitlyBound
checkForDuplicateNames = fmap ImplicitlyBound . flip execStateT mempty . mapM_ check
  where check (Id v) = seeing BoundAsVar (identName v) (srclocOf v)
        check (PatternParens p _) = check p
        check Wildcard{} = return ()
        check (TuplePattern ps _) = mapM_ check ps
        check (RecordPattern fs _) = mapM_ (check . snd) fs
        check (PatternAscription p t) = do
          check p
          checkForDuplicateNamesTypeExp' $ declaredType t

checkForDuplicateNamesTypeExp :: MonadTypeChecker m =>
                                 ImplicitlyBound
                              -> TypeExp Name -> m ImplicitlyBound
checkForDuplicateNamesTypeExp (ImplicitlyBound implicit) te =
  ImplicitlyBound <$> execStateT (checkForDuplicateNamesTypeExp' te) implicit

checkForDuplicateNamesTypeExp' :: MonadTypeChecker m =>
                                  TypeExp Name
                               -> StateT (M.Map (Namespace, Name) (VName, Bindage, SrcLoc)) m ()
checkForDuplicateNamesTypeExp' TEVar{} = return ()
checkForDuplicateNamesTypeExp' (TERecord fs _) =
  mapM_ (checkForDuplicateNamesTypeExp' . snd) fs
checkForDuplicateNamesTypeExp' (TETuple ts _) =
  mapM_ checkForDuplicateNamesTypeExp' ts
checkForDuplicateNamesTypeExp' (TEUnique t _) =
  checkForDuplicateNamesTypeExp' t
checkForDuplicateNamesTypeExp' (TEArray te d loc) =
  checkForDuplicateNamesTypeExp' te >> checkDimDecl d
  where checkDimDecl AnyDim = return ()
        checkDimDecl (ConstDim _) = return ()
        checkDimDecl (NamedDim (QualName [] v)) = seeing UsedFree v loc
        checkDimDecl (NamedDim _) = return ()
        checkDimDecl (BoundDim v) = seeing BoundAsDim v loc
        checkDimDecl e@(ArithDim op l r) = do
          l' <- checkRDimDecl l
          r' <- checkRDimDecl r
          case (l', r') of
            ((), ()) -> return ()
            _ -> throwError $ TypeError loc $ "Error in arithmetic dim" ++ pretty e

        checkRDimDecl (RConstDim _) = return ()
        checkRDimDecl (RNamedDim (QualName [] v)) = seeing UsedFree v loc
        checkRDimDecl (RNamedDim _) = return ()
        checkRDimDecl e@(RArithDim op l r) = do
          l' <- checkRDimDecl l
          r' <- checkRDimDecl r
          case (l', r') of
            ((), ()) -> return ()
            _ -> throwError $ TypeError loc $ "Error in arithmetic dim" ++ pretty e

seeing :: MonadTypeChecker m => Bindage -> Name -> SrcLoc
       -> StateT (M.Map (Namespace, Name) (VName, Bindage, SrcLoc)) m ()
seeing b v vloc = do
  seen <- get
  case (b, M.lookup (Term, v) seen) of
    (BoundAsDim, Just (_, BoundAsDim, _)) ->
      return ()
    (BoundAsDim, Just (_, UsedFree, loc)) ->
      throwError $ TypeError vloc $ "Name " ++ pretty v ++
        " previously used free at " ++ locStr loc
    (UsedFree, Just (_, BoundAsDim, loc)) ->
      throwError $ TypeError vloc $ "Name " ++ pretty v ++
        " previously implicitly bound at " ++ locStr loc
    (UsedFree, sb) -> do
      v' <- lift $ checkName Term v vloc
      when (isNothing sb) $
        modify $ M.insert (Term, v) (v', b, vloc)
    (BoundAsVar, Just (_, BoundAsDim, loc)) ->
      throwError $ DupPatternError v vloc loc
    (BoundAsVar, Just (_, UsedFree, loc)) ->
      throwError $ TypeError vloc $ "Name " ++ pretty v ++
      "bound here, but also referenced at " ++ locStr loc
    (_, Just (_, BoundAsVar, loc)) ->
      throwError $ DupPatternError v vloc loc
    (_, Nothing) -> newlyBound b v vloc

  where newlyBound b name vloc = do
          name' <- lift $ newID name
          modify $ M.insert (Term, name) (name', b, vloc)
