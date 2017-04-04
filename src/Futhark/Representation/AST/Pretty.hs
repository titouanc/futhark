{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
-- | Futhark prettyprinter.  This module defines 'Pretty' instances
-- for the AST defined in "Futhark.Representation.AST.Syntax",
-- but also a number of convenience functions if you don't want to use
-- the interface from 'Pretty'.
module Futhark.Representation.AST.Pretty
  ( prettyTuple
  , pretty
  , PrettyAnnot (..)
  , PrettyLore (..)
  , ppCertificates
  , ppCertificates'
  , ppTuple'
  , bindingAnnotation
  , ppArray
  )
  where

import           Data.Array                                     (elems,
                                                                 listArray)
import           Data.Maybe
import           Data.Monoid

import           Futhark.Util.Pretty

import           Futhark.Representation.AST.Attributes.Patterns
import           Futhark.Representation.AST.Syntax
import           Futhark.Util

-- | Class for values that may have some prettyprinted annotation.
class PrettyAnnot a where
  ppAnnot :: a -> Maybe Doc

instance PrettyAnnot (PatElemT (TypeBase shape u)) where
  ppAnnot = const Nothing

instance PrettyAnnot (ParamT (TypeBase shape u)) where
  ppAnnot = const Nothing

instance PrettyAnnot () where
  ppAnnot = const Nothing

-- | The class of lores whose annotations can be prettyprinted.
class (Annotations lore,
       Pretty (RetType lore),
       Pretty (ParamT (FParamAttr lore)),
       Pretty (ParamT (LParamAttr lore)),
       Pretty (PatElemT (LetAttr lore)),
       PrettyAnnot (PatElem lore),
       PrettyAnnot (FParam lore),
       PrettyAnnot (LParam lore),
       Pretty (Op lore)) => PrettyLore lore where
  ppExpLore :: ExpAttr lore -> Exp lore -> Maybe Doc
  ppExpLore = const $ const Nothing

commastack :: [Doc] -> Doc
commastack = align . stack . punctuate comma

instance Pretty NoUniqueness where
  ppr _ = mempty

instance Pretty Commutativity where
  ppr Commutative    = text "commutative"
  ppr Noncommutative = text "noncommutative"

-- | Print an array value, using the given function for printing
-- elements.
ppArray :: (PrimValue -> Doc) -> Value -> Doc
ppArray pprim (PrimVal v) = pprim v
ppArray _ (ArrayVal _ t shape)
  | product shape == 0 = text "empty" <> parens (ppr row_t)
  where row_t = Array t (Rank $ length shape - 1) NoUniqueness
ppArray pprim (ArrayVal a t (_:rowshape@(_:_))) =
  brackets $ commastack
  [ ppArray pprim $ ArrayVal (listArray (0, rowsize-1) a') t rowshape
  | a' <- chunk rowsize $ elems a ]
  where rowsize = product rowshape
ppArray pprim (ArrayVal a _ _) =
  brackets $ commasep $ map pprim $ elems a

instance Pretty Value where
  ppr = ppArray ppr

instance Pretty Shape where
  ppr = brackets . commasep . map ppr . shapeDims

instance Pretty ExtDimSize where
  ppr (Free e) = ppr e
  ppr (Ext x)  = text "?" <> text (show x)

instance Pretty ExtShape where
  ppr = brackets . commasep . map ppr . extShapeDims

instance Pretty Space where
  ppr DefaultSpace = mempty
  ppr (Space s)    = text "@" <> text s

instance Pretty u => Pretty (TypeBase Shape u) where
  ppr (Prim et) = ppr et
  ppr (Array et (Shape ds) u) =
    ppr u <> mconcat (map (brackets . ppr) ds) <> ppr et
  ppr (Mem s DefaultSpace) = text "mem" <> parens (ppr s)
  ppr (Mem s (Space sp)) = text "mem" <> parens (ppr s) <> text "@" <> text sp

instance Pretty u => Pretty (TypeBase ExtShape u) where
  ppr (Prim et) = ppr et
  ppr (Array et (ExtShape ds) u) =
    ppr u <> mconcat (map (brackets . ppr) ds) <> ppr et
  ppr (Mem s DefaultSpace) = text "mem" <> parens (ppr s)
  ppr (Mem s (Space sp)) = text "mem" <> parens (ppr s) <> text "@" <> text sp

instance Pretty u => Pretty (TypeBase Rank u) where
  ppr (Prim et) = ppr et
  ppr (Array et (Rank n) u) =
    ppr u <> mconcat (replicate n $ brackets mempty) <> ppr et
  ppr (Mem s DefaultSpace) = text "mem" <> parens (ppr s)
  ppr (Mem s (Space sp)) = text "mem" <> parens (ppr s) <> text "@" <> text sp

instance Pretty Ident where
  ppr ident = ppr (identType ident) <+> ppr (identName ident)

instance Pretty SubExp where
  ppr (Var v)      = ppr v
  ppr (Constant v) = ppr v

instance PrettyLore lore => Pretty (Body lore) where
  ppr (Body _ (bnd:bnds) res) =
    stack (map ppr (bnd:bnds)) </>
    text "in" <+> braces (commasep $ map ppr res)
  ppr (Body _ [] res) =
    braces (commasep $ map ppr res)

bindingAnnotation :: PrettyLore lore => Stm lore -> Doc -> Doc
bindingAnnotation bnd =
  case mapMaybe ppAnnot $ patternElements $ bindingPattern bnd of
    []     -> id
    annots -> (stack annots </>)

instance Pretty (PatElemT attr) => Pretty (PatternT attr) where
  ppr pat = ppPattern (patternContextElements pat) (patternValueElements pat)

instance Pretty (PatElemT b) => Pretty (PatElemT (a,b)) where
  ppr = ppr . fmap snd

instance Pretty (PatElemT Type) where
  ppr (PatElem name BindVar t) =
    ppr t <+>
    ppr name

  ppr (PatElem name (BindInPlace cs src is) t) =
    ppCertificates cs <>
    parens (ppr t <+>
            ppr name <+>
            text "<-" <+>
            ppr src) <>
    brackets (commasep $ map ppr is)

instance Pretty (ParamT b) => Pretty (ParamT (a,b)) where
  ppr = ppr . fmap snd

instance Pretty (ParamT DeclType) where
  ppr (Param name t) =
    ppr t <+>
    ppr name

instance Pretty (ParamT Type) where
  ppr (Param name t) =
    ppr t <+>
    ppr name

instance PrettyLore lore => Pretty (Stm lore) where
  ppr bnd@(Let pat attr e) =
    bindingAnnotation bnd $ align $
    text "let" <+> align (ppr pat) <+>
    case (linebreak, ppExpLore attr e) of
      (True, Nothing) -> equals </>
                         indent 2 e'
      (_, Just ann) -> equals </>
                       indent 2 (ann </> e')
      (False, Nothing) -> equals <+> align e'
    where e' = ppr e
          linebreak = case e of
                        DoLoop{}           -> True
                        Op{}               -> True
                        If{}               -> True
                        BasicOp ArrayLit{} -> False
                        _                  -> False

instance Pretty (BasicOp lore) where
  ppr (SubExp se) = ppr se
  ppr (Opaque e) = text "opaque" <> apply [ppr e]
  ppr (ArrayLit [] rt) =
    text "empty" <> parens (ppr rt)
  ppr (ArrayLit es rt) =
    case rt of
      Array {} -> brackets $ commastack $ map ppr es
      _        -> brackets $ commasep   $ map ppr es
  ppr (BinOp bop x y) = ppr bop <> parens (ppr x <> comma <+> ppr y)
  ppr (CmpOp op x y) = ppr op <> parens (ppr x <> comma <+> ppr y)
  ppr (ConvOp conv x) =
    text (convOpFun conv) <+> ppr fromtype <+> ppr x <+> text "to" <+> ppr totype
    where (fromtype, totype) = convTypes conv
  ppr (UnOp op e) = ppr op <+> pprPrec 9 e
  ppr (Index cs v idxs) =
    ppCertificates cs <> ppr v <>
    brackets (commasep (map ppr idxs))
  ppr (Iota e x s et) = text "iota" <> et' <> apply [ppr e, ppr x, ppr s]
    where et' = text $ show $ primBitSize $ IntType et
  ppr (Replicate ne ve) =
    text "replicate" <> apply [ppr ne, align (ppr ve)]
  ppr (Scratch t shape) =
    text "scratch" <> apply (ppr t : map ppr shape)
  ppr (Reshape cs shape e) =
    ppCertificates cs <> text "reshape" <> apply [apply (map ppr shape), ppr e]
  ppr (Rearrange cs perm e) =
    ppCertificates cs <> text "rearrange" <> apply [apply (map ppr perm), ppr e]
  ppr (Rotate cs es e) =
    ppCertificates cs <> text "rotate" <> apply [apply (map ppr es), ppr e]
  ppr (Split cs i sizeexps a) =
    ppCertificates cs <> text "split" <> text "@" <> ppr i <> apply [apply (map ppr sizeexps), ppr a]
  ppr (Concat cs i x ys _) =
    ppCertificates cs <> text "concat" <> text "@" <> ppr i <> apply (ppr x : map ppr ys)
  ppr (Copy e) = text "copy" <> parens (ppr e)
  ppr (Manifest perm e) = text "manifest" <> apply [apply (map ppr perm), ppr e]
  ppr (Assert e loc) = text "assert" <> apply [ppr e, text $ show $ locStr loc]
  ppr (Partition cs n flags arrs) =
    ppCertificates' cs <>
    text "partition" <>
    parens (commasep $ [ ppr n, ppr flags ] ++ map ppr arrs)

instance PrettyLore lore => Pretty (Exp lore) where
  ppr (If c t f _) = text "if" <+> ppr c </>
                     text "then" <+> align (ppr t) </>
                     text "else" <+> align (ppr f)
  ppr (BasicOp op) = ppr op
  ppr (Apply fname args _) = text (nameToString fname) <>
                             apply (map (align . ppr . fst) args)
  ppr (Op op) = ppr op
  ppr (DoLoop ctx val form loopbody) =
    annot (mapMaybe ppAnnot (ctxparams++valparams)) $
    text "loop" <+> ppPattern ctxparams valparams <+>
    equals <+> ppTuple' (ctxinit++valinit) </>
    (case form of
      ForLoop i it bound ->
        text "for" <+> ppr i <> text ":" <> ppr it <+> text "<" <+> align (ppr bound)
      WhileLoop cond ->
        text "while" <+> ppr cond
    ) <+> text "do" <+> nestedBlock "{" "}" (ppr loopbody)
    where (ctxparams, ctxinit) = unzip ctx
          (valparams, valinit) = unzip val

instance PrettyLore lore => Pretty (Lambda lore) where
  ppr (Lambda params body rettype) =
    annot (mapMaybe ppAnnot params) $
    text "fn" <+> ppTuple' rettype <+>
    parens (commasep (map ppr params)) <+>
    text "=>" </> indent 2 (ppr body)

instance PrettyLore lore => Pretty (ExtLambda lore) where
  ppr (ExtLambda params body rettype) =
    text "fn" <+> ppTuple' rettype <+>
    parens (commasep (map ppr params)) <+>
    text "=>" </> indent 2 (ppr body)

instance Pretty ExtRetType where
  ppr = ppTuple' . retTypeValues

instance PrettyLore lore => Pretty (FunDef lore) where
  ppr (FunDef entry name rettype fparams body) =
    annot (mapMaybe ppAnnot fparams) $
    text fun <+> ppr rettype <+>
    text (nameToString name) <//>
    apply (map ppr fparams) <+>
    equals </> indent 2 (ppr body)
    where fun | isJust entry = "entry"
              | otherwise    = "fun"

instance PrettyLore lore => Pretty (Prog lore) where
  ppr = stack . punctuate line . map ppr . progFunctions

instance Pretty d => Pretty (DimChange d) where
  ppr (DimCoercion se) = text "~" <> ppr se
  ppr (DimNew      se) = ppr se

instance Pretty d => Pretty (DimIndex d) where
  ppr (DimFix i)       = ppr i
  ppr (DimSlice i n s) = ppr i <> text ":+" <> ppr n <> text "*" <> ppr s

ppPattern :: (Pretty a, Pretty b) => [a] -> [b] -> Doc
ppPattern [] bs = braces $ commasep $ map ppr bs
ppPattern as bs = braces $ commasep (map ppr as) <> semi <+> commasep (map ppr bs)

ppTuple' :: Pretty a => [a] -> Doc
ppTuple' ets = braces $ commasep $ map ppr ets

ppCertificates :: Certificates -> Doc
ppCertificates [] = empty
ppCertificates cs = text "<" <> commasep (map ppr cs) <> text ">"

ppCertificates' :: Certificates -> Doc
ppCertificates' [] = empty
ppCertificates' cs = ppCertificates cs <> line
