{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
-- | Definition of the lore used by the simplification engine.
module Futhark.Optimise.Simplifier.Lore
       (
         Wise
       , VarWisdom (..)
       , removeStmWisdom
       , removeLambdaWisdom
       , removeExtLambdaWisdom
       , removeProgWisdom
       , removeFunDefWisdom
       , removeExpWisdom
       , removePatternWisdom
       , removePatElemWisdom
       , removeBodyWisdom
       , removeScopeWisdom
       , addScopeWisdom
       , addWisdomToPattern
       , mkWiseBody
       , mkWiseLetStm

       , CanBeWise (..)
       )
       where

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Monoid
import qualified Data.Map.Strict as M

import Prelude

import Futhark.Representation.AST
import Futhark.Representation.AST.Attributes.Ranges
import Futhark.Representation.AST.Attributes.Aliases
import Futhark.Representation.Aliases
  (unNames, Names' (..), VarAliases, ConsumedInExp)
import qualified Futhark.Representation.Aliases as Aliases
import qualified Futhark.Representation.Ranges as Ranges
import Futhark.Binder
import Futhark.Transform.Rename
import Futhark.Transform.Substitute
import Futhark.Analysis.Rephrase
import Futhark.Analysis.Usage (UsageInOp)

data Wise lore

-- | The wisdom of the let-bound variable.
data VarWisdom = VarWisdom { varWisdomAliases :: VarAliases
                           , varWisdomRange :: Range
                           }
                  deriving (Eq, Ord, Show)

instance Rename VarWisdom where
  rename = substituteRename

instance Substitute VarWisdom where
  substituteNames substs (VarWisdom als range) =
    VarWisdom (substituteNames substs als) (substituteNames substs range)

instance FreeIn VarWisdom where
  freeIn (VarWisdom als range) = freeIn als <> freeIn range

-- | Wisdom about an expression.
data ExpWisdom = ExpWisdom { _expWisdomConsumed :: ConsumedInExp
                           , expWisdomFree :: Names'
                           }
                 deriving (Eq, Ord, Show)

instance FreeIn ExpWisdom where
  freeIn = mempty

instance FreeAttr ExpWisdom where
  precomputed = const . unNames . expWisdomFree

instance Substitute ExpWisdom where
  substituteNames substs (ExpWisdom cons free) =
    ExpWisdom
    (substituteNames substs cons)
    (substituteNames substs free)

instance Rename ExpWisdom where
  rename = substituteRename

-- | Wisdom about a body.
data BodyWisdom = BodyWisdom { bodyWisdomAliases :: [VarAliases]
                             , bodyWisdomConsumed :: ConsumedInExp
                             , bodyWisdomRanges :: [Range]
                             , bodyWisdomFree :: Names'
                             }
                  deriving (Eq, Ord, Show)

instance Rename BodyWisdom where
  rename = substituteRename

instance Substitute BodyWisdom where
  substituteNames substs (BodyWisdom als cons rs free) =
    BodyWisdom
    (substituteNames substs als)
    (substituteNames substs cons)
    (substituteNames substs rs)
    (substituteNames substs free)

instance FreeIn BodyWisdom where
  freeIn (BodyWisdom als cons rs free) =
    freeIn als <> freeIn cons <> freeIn rs <> freeIn free

instance FreeAttr BodyWisdom where
  precomputed = const . unNames . bodyWisdomFree

instance (Annotations lore,
          CanBeWise (Op lore)) => Annotations (Wise lore) where
  type LetAttr (Wise lore) = (VarWisdom, LetAttr lore)
  type ExpAttr (Wise lore) = (ExpWisdom, ExpAttr lore)
  type BodyAttr (Wise lore) = (BodyWisdom, BodyAttr lore)
  type FParamAttr (Wise lore) = FParamAttr lore
  type LParamAttr (Wise lore) = LParamAttr lore
  type RetType (Wise lore) = RetType lore
  type Op (Wise lore) = OpWithWisdom (Op lore)

instance (Attributes lore, CanBeWise (Op lore)) => Attributes (Wise lore) where
  expContext pat e = do
    types <- asksScope removeScopeWisdom
    runReaderT (expContext (removePatternWisdom pat) (removeExpWisdom e)) types

instance PrettyAnnot (PatElemT attr) => PrettyAnnot (PatElemT (VarWisdom, attr)) where
  ppAnnot = ppAnnot . fmap snd

instance (PrettyLore lore, CanBeWise (Op lore)) => PrettyLore (Wise lore) where
  ppExpLore (_, attr) = ppExpLore attr . removeExpWisdom

instance AliasesOf (VarWisdom, attr) where
  aliasesOf = unNames . varWisdomAliases . fst

instance RangeOf (VarWisdom, attr) where
  rangeOf = varWisdomRange . fst

instance RangesOf (BodyWisdom, attr) where
  rangesOf = bodyWisdomRanges . fst

instance (Attributes lore, CanBeWise (Op lore)) => Aliased (Wise lore) where
  bodyAliases = map unNames . bodyWisdomAliases . fst . bodyLore
  consumedInBody = unNames . bodyWisdomConsumed . fst . bodyLore

removeWisdom :: CanBeWise (Op lore) => Rephraser Identity (Wise lore) lore
removeWisdom = Rephraser { rephraseExpLore = return . snd
                         , rephraseLetBoundLore = return . snd
                         , rephraseBodyLore = return . snd
                         , rephraseFParamLore = return
                         , rephraseLParamLore = return
                         , rephraseRetType = return
                         , rephraseOp = return . removeOpWisdom
                         }

removeScopeWisdom :: Scope (Wise lore) -> Scope lore
removeScopeWisdom = M.map unAlias
  where unAlias (LetInfo (_, attr)) = LetInfo attr
        unAlias (FParamInfo attr) = FParamInfo attr
        unAlias (LParamInfo attr) = LParamInfo attr
        unAlias (IndexInfo it) = IndexInfo it

addScopeWisdom :: Scope lore -> Scope (Wise lore)
addScopeWisdom = M.map alias
  where alias (LetInfo attr) = LetInfo (VarWisdom mempty unknownRange, attr)
        alias (FParamInfo attr) = FParamInfo attr
        alias (LParamInfo attr) = LParamInfo attr
        alias (IndexInfo it) = IndexInfo it

removeProgWisdom :: CanBeWise (Op lore) => Prog (Wise lore) -> Prog lore
removeProgWisdom = runIdentity . rephraseProg removeWisdom

removeFunDefWisdom :: CanBeWise (Op lore) => FunDef (Wise lore) -> FunDef lore
removeFunDefWisdom = runIdentity . rephraseFunDef removeWisdom

removeStmWisdom :: CanBeWise (Op lore) => Stm (Wise lore) -> Stm lore
removeStmWisdom = runIdentity . rephraseStm removeWisdom

removeLambdaWisdom :: CanBeWise (Op lore) => Lambda (Wise lore) -> Lambda lore
removeLambdaWisdom = runIdentity . rephraseLambda removeWisdom

removeExtLambdaWisdom :: CanBeWise (Op lore) => ExtLambda (Wise lore) -> ExtLambda lore
removeExtLambdaWisdom = runIdentity . rephraseExtLambda removeWisdom

removeBodyWisdom :: CanBeWise (Op lore) => Body (Wise lore) -> Body lore
removeBodyWisdom = runIdentity . rephraseBody removeWisdom

removeExpWisdom :: CanBeWise (Op lore) => Exp (Wise lore) -> Exp lore
removeExpWisdom = runIdentity . rephraseExp removeWisdom

removePatternWisdom :: PatternT (VarWisdom, a) -> PatternT a
removePatternWisdom = runIdentity . rephrasePattern (return . snd)

removePatElemWisdom :: PatElemT (VarWisdom, a) -> PatElemT a
removePatElemWisdom = runIdentity . rephrasePatElem (return . snd)

addWisdomToPattern :: (Attributes lore, CanBeWise (Op lore)) =>
                      Pattern lore
                   -> Exp (Wise lore)
                   -> Pattern (Wise lore)
addWisdomToPattern pat e =
  Pattern
  (map (`addRanges` unknownRange) ctxals)
  (zipWith addRanges valals ranges)
  where (ctxals, valals) = Aliases.mkPatternAliases pat e
        addRanges patElem range =
          let (als, innerlore) = patElemAttr patElem
          in patElem `setPatElemLore` (VarWisdom als range, innerlore)
        ranges = expRanges e

mkWiseBody :: (Attributes lore, CanBeWise (Op lore)) =>
              BodyAttr lore -> [Stm (Wise lore)] -> Result -> Body (Wise lore)
mkWiseBody innerlore bnds res =
  Body (BodyWisdom aliases consumed ranges (Names' $ freeInStmsAndRes bnds res),
        innerlore) bnds res
  where (aliases, consumed) = Aliases.mkBodyAliases bnds res
        ranges = Ranges.mkBodyRanges bnds res

mkWiseLetStm :: (Attributes lore, CanBeWise (Op lore)) =>
                Pattern lore
             -> ExpAttr lore -> Exp (Wise lore)
             -> Stm (Wise lore)
mkWiseLetStm pat explore e =
  Let (addWisdomToPattern pat e)
  (ExpWisdom
    (Names' $ consumedInPattern pat <> consumedInExp e)
    (Names' $ freeIn pat <> freeIn explore <> freeInExp e),
   explore)
  e

instance (Bindable lore,
          CanBeWise (Op lore)) => Bindable (Wise lore) where
  mkLet context values e =
    let Let pat' explore _ = mkLet context values $ removeExpWisdom e
    in mkWiseLetStm pat' explore e

  mkLetNames names e = do
    env <- asksScope removeScopeWisdom
    flip runReaderT env $ do
      Let pat explore _ <- mkLetNames names $ removeExpWisdom e
      return $ mkWiseLetStm pat explore e

  mkBody bnds res =
    let Body bodylore _ _ = mkBody (map removeStmWisdom bnds) res
    in mkWiseBody bodylore bnds res

class (AliasedOp (OpWithWisdom op),
       RangedOp (OpWithWisdom op),
       IsOp (OpWithWisdom op),
       UsageInOp (OpWithWisdom op)) => CanBeWise op where
  type OpWithWisdom op :: *
  removeOpWisdom :: OpWithWisdom op -> op

instance CanBeWise () where
  type OpWithWisdom () = ()
  removeOpWisdom () = ()
