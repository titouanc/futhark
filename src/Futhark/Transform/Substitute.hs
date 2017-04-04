{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
-- |
--
-- This module contains facilities for replacing variable names in
-- syntactic constructs.
module Futhark.Transform.Substitute
  (Substitutions,
   Substitute(..),
   Substitutable)
  where

import Control.Monad.Identity
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Futhark.Representation.AST.Syntax
import Futhark.Representation.AST.Traversals
import Futhark.Representation.AST.Attributes.Scope
import Futhark.Analysis.PrimExp

-- | The substitutions to be made are given by a mapping from names to
-- names.
type Substitutions = M.Map VName VName

-- | A type that is an instance of this class supports substitution of
-- any names contained within.
class Substitute a where
  -- | @substituteNames m e@ replaces the variable names in @e@ with
  -- new names, based on the mapping in @m@.  It is assumed that all
  -- names in @e@ are unique, i.e. there is no shadowing.
  substituteNames :: M.Map VName VName -> a -> a

instance Substitute a => Substitute [a] where
  substituteNames substs = map $ substituteNames substs

instance (Substitute a, Substitute b) => Substitute (a,b) where
  substituteNames substs (x,y) =
    (substituteNames substs x, substituteNames substs y)

instance (Substitute a, Substitute b, Substitute c) => Substitute (a,b,c) where
  substituteNames substs (x,y,z) =
    (substituteNames substs x,
     substituteNames substs y,
     substituteNames substs z)

instance (Substitute a, Substitute b, Substitute c, Substitute d) => Substitute (a,b,c,d) where
  substituteNames substs (x,y,z,u) =
    (substituteNames substs x,
     substituteNames substs y,
     substituteNames substs z,
     substituteNames substs u)

instance Substitute a => Substitute (Maybe a) where
  substituteNames substs = fmap $ substituteNames substs

instance Substitute Bool where
  substituteNames = flip const

instance Substitute VName where
  substituteNames substs k = M.findWithDefault k k substs

instance Substitute SubExp where
  substituteNames substs (Var v) = Var $ substituteNames substs v
  substituteNames _ (Constant v) = Constant v

instance Substitutable lore => Substitute (Exp lore) where
  substituteNames substs = mapExp $ replace substs

instance Substitute attr => Substitute (PatElemT attr) where
  substituteNames substs (PatElem ident bindage attr) =
    PatElem
    (substituteNames substs ident)
    (substituteNames substs bindage)
    (substituteNames substs attr)

instance Substitute Bindage where
  substituteNames _ BindVar =
    BindVar
  substituteNames substs (BindInPlace cs src is) =
    BindInPlace
    (map (substituteNames substs) cs)
    (substituteNames substs src)
    (map (substituteNames substs) is)

instance Substitute attr => Substitute (ParamT attr) where
  substituteNames substs (Param name attr) =
    Param
    (substituteNames substs name)
    (substituteNames substs attr)

instance Substitute attr => Substitute (PatternT attr) where
  substituteNames substs (Pattern context values) =
    Pattern (substituteNames substs context) (substituteNames substs values)

instance Substitutable lore => Substitute (Stm lore) where
  substituteNames substs (Let pat annot e) =
    Let
    (substituteNames substs pat)
    (substituteNames substs annot)
    (substituteNames substs e)

instance Substitutable lore => Substitute (Body lore) where
  substituteNames substs (Body attr bnds res) =
    Body
    (substituteNames substs attr)
    (substituteNames substs bnds)
    (substituteNames substs res)
{-
instance Substitutable lore => Substitute (FunDef lore) where
  substituteNames substs (FunDef entry name ret ps body) =
    FunDef entry
      (substituteNames substs name)
      (substituteNames substs ret)
      (substituteNames substs ps)
      (substituteNames substs body)
-}
replace :: (Substitutable lore) => M.Map VName VName -> Mapper lore lore Identity
replace substs = Mapper {
                   mapOnVName = return . substituteNames substs
                 , mapOnSubExp = return . substituteNames substs
                 , mapOnBody = const $ return . substituteNames substs
                 , mapOnCertificates = return . map (substituteNames substs)
                 , mapOnRetType = return . substituteNames substs
                 , mapOnFParam = return . substituteNames substs
                 , mapOnOp = return . substituteNames substs
                 }

instance Substitute Rank where
  substituteNames _ = id

instance Substitute () where
  substituteNames _ = id

instance Substitute Shape where
  substituteNames substs (Shape es) =
    Shape $ map (substituteNames substs) es

instance Substitute ExtShape where
  substituteNames substs (ExtShape es) =
    ExtShape $ map (substituteNames substs) es

instance Substitute ExtDimSize where
  substituteNames substs (Free se) = Free $ substituteNames substs se
  substituteNames _      (Ext x)   = Ext x

instance Substitute Names where
  substituteNames = S.map . substituteNames

instance Substitute shape => Substitute (TypeBase shape u) where
  substituteNames _ (Prim et) = Prim et
  substituteNames substs (Array et sz u) =
    Array et (substituteNames substs sz) u
  substituteNames substs (Mem sz space) =
    Mem (substituteNames substs sz) space

instance Substitutable lore => Substitute (Lambda lore) where
  substituteNames substs (Lambda params body rettype) =
    Lambda
    (substituteNames substs params)
    (substituteNames substs body)
    (map (substituteNames substs) rettype)

instance Substitutable lore => Substitute (ExtLambda lore) where
  substituteNames substs (ExtLambda params body rettype) =
    ExtLambda
    (substituteNames substs params)
    (substituteNames substs body)
    (map (substituteNames substs) rettype)

instance Substitute Ident where
  substituteNames substs v =
    v { identName = substituteNames substs $ identName v
      , identType = substituteNames substs $ identType v
      }

instance Substitute ExtRetType where
  substituteNames substs (ExtRetType ts) =
    ExtRetType $ map (substituteNames substs) ts

instance Substitute d => Substitute (DimChange d) where
  substituteNames substs = fmap $ substituteNames substs

instance Substitute d => Substitute (DimIndex d) where
  substituteNames substs = fmap $ substituteNames substs

instance Substitute v => Substitute (PrimExp v) where
  substituteNames substs = fmap $ substituteNames substs

instance Substitutable lore => Substitute (NameInfo lore) where
  substituteNames subst (LetInfo attr) =
    LetInfo $ substituteNames subst attr
  substituteNames subst (FParamInfo attr) =
    FParamInfo $ substituteNames subst attr
  substituteNames subst (LParamInfo attr) =
    LParamInfo $ substituteNames subst attr
  substituteNames _ (IndexInfo it) =
    IndexInfo it

-- | Lores in which all annotations support name
-- substitution.
type Substitutable lore = (Annotations lore,
                           Substitute (ExpAttr lore),
                           Substitute (BodyAttr lore),
                           Substitute (LetAttr lore),
                           Substitute (FParamAttr lore),
                           Substitute (LParamAttr lore),
                           Substitute (RetType lore),
                           Substitute (Op lore))
