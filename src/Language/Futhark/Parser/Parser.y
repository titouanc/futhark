{
{-# LANGUAGE OverloadedStrings  #-}
-- | Futhark parser written with Happy.
module Language.Futhark.Parser.Parser
  ( prog
  , expression
  , futharkType
  , anyValue
  , anyValues
  , ParserEnv (..)
  , ParserMonad
  , ReadLineMonad(..)
  , getLinesFromIO
  , getLinesFromTexts
  , getNoLines
  , newParserEnv

  , parse
  , ParseError(..)
  , parseExpIncr
  , parseExpIncrIO
  )
  where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Trans.State
import Control.Applicative ((<$>), (<*>))
import Control.Arrow
import Data.Array
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Char (ord)
import Data.Maybe (fromMaybe)
import Data.Loc hiding (L) -- Lexer has replacements.
import qualified Data.HashMap.Lazy as HM
import Data.Monoid

import Language.Futhark.Syntax hiding (ID)
import Language.Futhark.Attributes
import Language.Futhark.Pretty
import Language.Futhark.Parser.Lexer

}

%name prog Prog
%name futharkType TypeExp
%name expression Exp
%name lambda FunAbstr
%name anyValue Value
%name anyValues CatValues

%tokentype { L Token }
%error { parseError }
%monad { ParserMonad }
%lexer { lexer } { L _ EOF }

%token
      if              { L $$ IF }
      then            { L $$ THEN }
      else            { L $$ ELSE }
      let             { L $$ LET }
      loop            { L $$ LOOP }
      in              { L $$ IN }
      default         { L $$ DEFAULT }

      id              { L _ (ID _) }
      'id['           { L _ (INDEXING _) }

      qid             { L _ (QUALID _ _) }
      'qid['          { L _ (QUALINDEXING _ _) }

      unop            { L _ (UNOP _) }
      qunop           { L _ (QUALUNOP _ _) }

      declit          { L _ (DECLIT _) }
      intlit          { L _ (INTLIT _) }
      i8lit           { L _ (I8LIT _) }
      i16lit          { L _ (I16LIT _) }
      i32lit          { L _ (I32LIT _) }
      i64lit          { L _ (I64LIT _) }
      u8lit           { L _ (U8LIT _) }
      u16lit          { L _ (U16LIT _) }
      u32lit          { L _ (U32LIT _) }
      u64lit          { L _ (U64LIT _) }
      reallit         { L _ (REALLIT _) }
      f32lit          { L _ (F32LIT _) }
      f64lit          { L _ (F64LIT _) }
      stringlit       { L _ (STRINGLIT _) }
      charlit         { L _ (CHARLIT _) }

      '#'             { L $$ HASH }
      '='             { L $$ EQU }

      '*'             { L $$ ASTERISK }
      '-'             { L $$ NEGATE }
      '<'             { L $$ LTH }
      '>'             { L $$ GTH }
      '<='            { L $$ LEQ }
      '>='            { L $$ GEQ }

      '+...'          { L _ (SYMBOL Plus _ _) }
      '-...'          { L _ (SYMBOL Minus _ _) }
      '*...'          { L _ (SYMBOL Times _ _) }
      '/...'          { L _ (SYMBOL Divide _ _) }
      '%...'          { L _ (SYMBOL Mod _ _) }
      '//...'         { L _ (SYMBOL Quot _ _) }
      '%%...'         { L _ (SYMBOL Rem _ _) }
      '==...'         { L _ (SYMBOL Equal _ _) }
      '!=...'         { L _ (SYMBOL NotEqual _ _) }
      '<...'          { L _ (SYMBOL Less _ _) }
      '>...'          { L _ (SYMBOL Greater _ _) }
      '<=...'         { L _ (SYMBOL Leq _ _) }
      '>=...'         { L _ (SYMBOL Geq _ _) }
      '**...'         { L _ (SYMBOL Pow _ _) }
      '<<...'         { L _ (SYMBOL ShiftL _ _) }
      '>>...'         { L _ (SYMBOL ShiftR _ _) }
      '>>>...'        { L _ (SYMBOL ZShiftR _ _) }
      '|...'          { L _ (SYMBOL Bor _ _) }
      '&...'          { L _ (SYMBOL Band _ _) }
      '^...'          { L _ (SYMBOL Xor _ _) }
      '||...'         { L _ (SYMBOL LogOr _ _) }
      '&&...'         { L _ (SYMBOL LogAnd _ _) }

      '('             { L $$ LPAR }
      ')'             { L $$ RPAR }
      ')['            { L $$ RPAR_THEN_LBRACKET }
      '{'             { L $$ LCURLY }
      '}'             { L $$ RCURLY }
      '['             { L $$ LBRACKET }
      ']'             { L $$ RBRACKET }
      ','             { L $$ COMMA }
      '_'             { L $$ UNDERSCORE }
      '@'             { L $$ AT }
      '\\'            { L $$ BACKSLASH }
      fun             { L $$ FUN }
      entry           { L $$ ENTRY }
      '->'            { L $$ RIGHT_ARROW }
      '<-'            { L $$ LEFT_ARROW }
      ':'             { L $$ COLON }
      for             { L $$ FOR }
      do              { L $$ DO }
      with            { L $$ WITH }
      iota            { L $$ IOTA }
      shape           { L $$ SHAPE }
      replicate       { L $$ REPLICATE }
      map             { L $$ MAP }
      reduce          { L $$ REDUCE }
      reduceComm      { L $$ REDUCECOMM }
      reshape         { L $$ RESHAPE }
      rearrange       { L $$ REARRANGE }
      transpose       { L $$ TRANSPOSE }
      rotate          { L $$ ROTATE }
      zipWith         { L $$ ZIPWITH }
      zip             { L $$ ZIP }
      unzip           { L $$ UNZIP }
      unsafe          { L $$ UNSAFE }
      scan            { L $$ SCAN }
      split           { L $$ SPLIT }
      concat          { L $$ CONCAT }
      filter          { L $$ FILTER }
      partition       { L $$ PARTITION }
      true            { L $$ TRUE }
      false           { L $$ FALSE }
      empty           { L $$ EMPTY }
      copy            { L $$ COPY }
      while           { L $$ WHILE }
      streamMap       { L $$ STREAM_MAP }
      streamMapPer    { L $$ STREAM_MAPPER }
      streamRed       { L $$ STREAM_RED }
      streamRedPer    { L $$ STREAM_REDPER }
      streamSeq       { L $$ STREAM_SEQ }
      include         { L $$ INCLUDE }
      import          { L $$ IMPORT }
      write           { L $$ WRITE }
      type            { L $$ TYPE }
      module          { L $$ MODULE }
      val             { L $$ VAL }
      open            { L $$ OPEN }

%left bottom
%left ifprec letprec
%left ','
%left ':'
%left '<-'
%left '||...'
%left '&&...'
%left '<=' '<=...' '>=' '>=...' '>' '>...' '<' '<...' '==...' '!=...'
%left '&...' '^...' '|...'

%left '<<...' '>>...' '>>>...'
%left '+...' '-...' '-'

%left '*...' '*' '/...' '%...' '//...' '%%...'
%left '**...'
%right '->'
nonassoc with
%nonassoc '~' '!' f32 f64 int i8 i16 i32 i64 unsafe default
%nonassoc '['
%nonassoc Id
%left juxtprec
%left indexprec iota shape copy transpose rotate rearrange split shape reduce map scan filter partition zipWith streamRed streamRedPer streamMap streamMapPer streamSeq
%%

-- Some parameterized productions.  Left-recursive, as this is faster
-- in Happy, but does require us to reverse lists at the end.  This
-- allows us to use a more EBNF-style grammar.

many(p) :          { [] }
        | many1(p) { fst $1 : snd $1 }

many1(p) : many1_(p) { reverseNonempty $1 }
many1_(p) : p           { ($1, []) }
          | many1_(p) p { ($2, fst $1 : snd $1) }

sepBy(p,s) :             { [] }
           | sepBy1(p,s) { fst $1 : snd $1 }

sepBy1(p,s) : sepBy1_(p,s) { reverseNonempty $1 }
sepBy1_(p,s) : p                { ($1, []) }
             | sepBy1_(p,s) s p { ($3, fst $1 : snd $1) }

sepBy2(p,s) : p s sepBy1(p,s) { $1 : fst $3 : snd $3 }

-- The main parser.


Prog :: { UncheckedProg }
      : many(Dec) { Prog (concat $1) }
;


Dec :: { [UncheckedDec] }
    : Fun               { [ValDec $ FunDec $1] }
    | Const             { [ValDec $ ConstDec $1] }
    | TypeAbbr          { map TypeDec $1 }
    | SigBind           { [SigDec $1 ] }
    | StructBind        { [StructDec $1 ] }
    | FunctorBind       { [FunctorDec $1] }
    | DefaultDec        { [] }
    | import stringlit
      { let L loc (STRINGLIT s) = $2 in [OpenDec (ModImport s loc) [] $1] }
    | open many1(ModExpAtom)
      { [OpenDec (fst $2) (snd $2) $1] }
;


Aliases : id ',' Aliases
            { let L loc (ID name) = $1
                in (name,loc) : $3 }
        | id { let L loc (ID name) = $1
               in [(name,loc)] }
;

SigExp :: { UncheckedSigExp }
        : QualName            { let (v, loc) = $1 in SigVar v loc }
        | '{' many(Spec) '}'  { SigSpecs $2 $1 }
        | SigExp with TypeRef { SigWith $1 $3 $2 }
        | '(' SigExp ')'      { SigParens $2 $1 }
        | '(' id ':' SigExp ')' '->' SigExp
                              { let L _ (ID name) = $2
                                in SigArrow (Just name) $4 $7 $1 }
        | SigExp '->' SigExp  { SigArrow Nothing $1 $3 (srclocOf $1) }

TypeRef :: { TypeRefBase NoInfo Name }
         : QualName '=' TypeExpDecl { TypeRef (fst $1) $3 }

SigBind :: { SigBindBase NoInfo Name }
         : module type id '=' SigExp
          { let L pos (ID name) = $3
            in SigBind name $5 pos }

ModExp :: { UncheckedModExp }
        : import stringlit { let L _ (STRINGLIT s) = $2 in ModImport s $1 }
        | ModExp ':' SigExp
          { ModAscript $1 $3 NoInfo (srclocOf $1) }
        | '\\' '(' id ':' SigExp ')' maybeAscription(SimpleSigExp) '->' ModExp
          { let L _ (ID pname) = $3
            in ModLambda (pname, $5) $7 $9 $1 }
        | ModExpApply
          { $1 }
        | ModExpAtom
          { $1 }

ModExpApply :: { UncheckedModExp }
             : ModExpAtom ModExpAtom %prec juxtprec
               { ModApply $1 $2 NoInfo NoInfo (srclocOf $1) }
             | ModExpApply ModExpAtom %prec juxtprec
               { ModApply $1 $2 NoInfo NoInfo (srclocOf $1) }

ModExpAtom :: { UncheckedModExp }
            : '(' ModExp ')'
              { ModParens $2 $1 }
            | QualName
              { let (v, loc) = $1 in ModVar v loc }
            | '{' many(Dec) '}' { ModDecs (concat $2) $1 }

SimpleSigExp :: { UncheckedSigExp }
             : QualName            { let (v, loc) = $1 in SigVar v loc }
             | '(' SigExp ')'      { $2 }

StructBind :: { StructBindBase NoInfo Name }
           : module id maybeAscription(SigExp) '=' ModExp
             { let L pos (ID name) = $2
               in StructBind name (case $3 of {Just mty -> ModAscript $5 mty NoInfo pos;
                                               Nothing -> $5}) pos
             }

FunctorBind :: { FunctorBindBase NoInfo Name }
             : module id '(' id ':' SigExp ')' maybeAscription(SigExp) '=' ModExp
               { let L floc (ID fname) = $2; L ploc (ID pname) = $4
                 in FunctorBind fname (pname, $6) $8 $10 $1
               }

Spec :: { SpecBase NoInfo Name }
      : val id ':' SigTypeDecl
        { let L loc (ID name) = $2; (ps, r) = $4
          in ValSpec name ps r loc  }
      | val BindingBinOp ':' SigTypeDecl
        { let (ps, r) = $4
          in ValSpec $2 ps r $1  }
      | type id '=' TypeExpDecl
        { let L loc (ID name) = $2
          in TypeAbbrSpec (TypeBind name $4 loc) }
      | type id
        { let L loc (ID name) = $2
          in TypeSpec name loc }
      | module id ':' SigExp
        { let L _ (ID name) = $2
          in ModSpec name $4 $1 }
      | include SigExp
        { IncludeSpec $2 $1 }
;

DefaultDec :: { () }
           :  default '(' id ')' {% let L _ (ID s) = $3 in defaultType s  }
           |  default '(' id ',' id ')'
                {% let L _ (ID s1) = $3; L _ (ID s2) = $5 in defaultType s1 >> defaultType s2 }
;


-- Note that this production does not include Minus.
BinOp :: { QualName Name }
      : '+...'     { binOpName $1 }
      | '-...'     { binOpName $1 }
      | '*...'     { binOpName $1 }
      | '*'        { qualName (nameFromString "*") }
      | '/...'     { binOpName $1 }
      | '%...'     { binOpName $1 }
      | '//...'    { binOpName $1 }
      | '%%...'    { binOpName $1 }
      | '==...'    { binOpName $1 }
      | '!=...'    { binOpName $1 }
      | '<...'     { binOpName $1 }
      | '<=...'    { binOpName $1 }
      | '>...'     { binOpName $1 }
      | '>=...'    { binOpName $1 }
      | '&&...'    { binOpName $1 }
      | '||...'    { binOpName $1 }
      | '**...'    { binOpName $1 }
      | '^...'     { binOpName $1 }
      | '&...'     { binOpName $1 }
      | '|...'     { binOpName $1 }
      | '>>...'    { binOpName $1 }
      | '>>>...'   { binOpName $1 }
      | '<<...'    { binOpName $1 }

      | '<'     { QualName [] (nameFromString "<") }
      | '<='    { QualName [] (nameFromString "<=") }
      | '>'     { QualName [] (nameFromString ">") }
      | '>='    { QualName [] (nameFromString ">=") }

BindingBinOp :: { Name }
      : BinOp {% let QualName qs name = $1 in do
                   unless (null qs) $ fail "Cannot use a qualified name in binding position."
                   return name }
      | '-'   { nameFromString "-" }

Fun     : fun id many1(Param) maybeAscription(TypeExpDecl) '=' Exp
          { let L pos (ID name) = $2
            in FunBind (name==defaultEntryPoint) name (fmap declaredType $4) NoInfo
               (fst $3 : snd $3) $6 pos
          }

        | entry id many1(Param) maybeAscription(TypeExpDecl) '=' Exp
          { let L pos (ID name) = $2
            in FunBind True name (fmap declaredType $4) NoInfo (fst $3 : snd $3) $6 pos }

        | fun Param BindingBinOp Param maybeAscription(TypeExpDecl) '=' Exp
          { FunBind False $3 (fmap declaredType $5) NoInfo [$2,$4] $7 $1
          }
;

Const : val id ':' TypeExpDecl '=' Exp
        { let L loc (ID name) = $2
          in ConstBind name (Just $ declaredType $4) NoInfo $6 loc }
      | val id '=' Exp
        { let L loc (ID name) = $2
          in ConstBind name Nothing NoInfo $4 loc }

SigTypeDecl :: { ([TypeDeclBase NoInfo Name], TypeDeclBase NoInfo Name) }
             : TypeExpDecl
               { ([], $1) }
             | TypeExpDecl '->' SigTypeDecl
               { let (ts, t) = $3 in ($1 : ts, t) }

TypeExpDecl :: { TypeDeclBase NoInfo Name }
             : TypeExp { TypeDecl $1 NoInfo }

TypeAbbr :: { [TypeBindBase NoInfo Name] }
TypeAbbr : type Aliases '=' TypeExpDecl
                  { let aliases = $2
                    in map (\(name, loc) -> TypeBind name $4 loc) aliases }

TypeExp :: { UncheckedTypeExp }
         : '*' TypeExp             { TEUnique $2 $1 }
         | '[' DimDecl ']' TypeExp { TEArray $4 $2 $1 }
         | '(' ')'                 { TETuple [] $1 }
         | '(' TypeExp ')'         { $2 }
         | QualName                { TEVar (fst $1) (snd $1) }
         | '{' sepBy(FieldType, ',') '}'
           { TERecord $2 $1 }
         | '(' sepBy2(TypeExp, ',') ')'
           { TETuple $2 $1 }

FieldType : FieldId ':' TypeExp { (fst $1, $3) }

DimDecl :: { DimDecl Name }
        : id
          { let L _ (ID name) = $1
            in NamedDim name }
        | '+...' { error "lol, got here" }
        | DimDecl '+...' DimDecl
          { ArithDim Plus $1 $3 }
        | DimDecl '-...' DimDecl
          { ArithDim Minus $1 $3 }
        | declit
          { let L _ (DECLIT n) = $1
            in ConstDim (fromIntegral n) }
        | intlit
          { let L _ (INTLIT n) = $1
            in ConstDim (fromIntegral n) }
        | { AnyDim }

Param :: { PatternBase NoInfo Name }
Param : InnerPattern { $1 }

QualName :: { (QualName Name, SrcLoc) }
          : qid { let L loc (QUALID qs v) = $1 in (QualName qs v, loc) }
          | id  { let L loc (ID v) = $1 in (QualName [] v, loc) }

QualUnOpName :: { (QualName Name, SrcLoc) }
          : qunop { let L loc (QUALUNOP qs v) = $1 in (QualName qs v, loc) }
          | unop  { let L loc (UNOP v) = $1 in (QualName [] v, loc) }

-- Expressions are divided into several layers.  The first distinction
-- (between Exp and Exp2) is to factor out ascription, which we do not
-- permit inside array indices operations (there is an ambiguity with
-- array slices).
Exp :: { UncheckedExp }
     : Exp ':' TypeExpDecl { Ascript $1 $3 $2 }
     | Exp2 %prec ':'          { $1 }

Exp2 :: { UncheckedExp }
     : if Exp then Exp else Exp %prec ifprec
                      { If $2 $4 $6 NoInfo $1 }

     | LetExp %prec letprec { $1 }

     | iota Atom { Iota $2 $1 }

     | shape Atom { Shape $2 $1 }

     | replicate Atom Atom { Replicate $2 $3 $1 }

     | reshape Atom Atom
                      { Reshape $2 $3 $1 }

     | rearrange '(' NaturalInts ')' Atom
                      { Rearrange $3 $5 $1 }

     | transpose Atom
                      { Transpose $2 $1 }

     | rotate '@' NaturalInt Atom Atom { Rotate $3 $4 $5 $1 }

     | rotate Atom Atom
                      { Rotate 0 $2 $3 $1 }

     | split Atom Atom
                      { Split 0 $2 $3 $1 }

     | split '@' NaturalInt Atom Atom
                      { Split $3 $4 $5 $1 }

     | concat many1(Atom)
                      { Concat 0 (fst $2) (snd $2) $1 }

     | concat '@' NaturalInt many1(Atom)
                      { Concat $3 (fst $4) (snd $4) $1 }


     | reduce FunAbstr Atom Atom
                      { Reduce Noncommutative $2 $3 $4 $1 }

     | reduceComm FunAbstr Atom Atom
                      { Reduce Commutative $2 $3 $4 $1 }


     | map FunAbstr many1(Atom)
                      { Map $2 (fst $3:snd $3) $1 }

     | zipWith FunAbstr many1(Atom)
                      { Map $2 (fst $3:snd $3) $1 }

     | scan FunAbstr Atom Atom
                      { Scan $2 $3 $4 $1 }

     | zip many1(Atom)
                      { Zip 0 (fst $2) (snd $2) $1 }

     | zip '@' NaturalInt many1(Atom)
                      { Zip $3 (fst $4) (snd $4) $1 }

     | unzip Atom  { Unzip $2 [] $1 }

     | unsafe Exp2     { Unsafe $2 $1 }

     | filter FunAbstr Atom
                      { Filter $2 $3 $1 }

     | partition '(' sepBy1(FunAbstr, ',') ')' Atom
                      { Partition (fst $3 : snd $3) $5 $1 }

     | copy Atom   { Copy $2 $1 }

     | streamMap       FunAbstr Atom
                         { Stream (MapLike InOrder)  $2 $3 $1 }
     | streamMapPer    FunAbstr Atom
                         { Stream (MapLike Disorder) $2 $3 $1 }
     | streamRed       FunAbstr FunAbstr Atom
                         { Stream (RedLike InOrder Noncommutative $2) $3 $4 $1 }
     | streamRedPer    FunAbstr FunAbstr Atom
                         { Stream (RedLike Disorder Commutative $2) $3 $4 $1 }
     | streamSeq       FunAbstr Atom Atom
                         { Stream (Sequential $3) $2 $4 $1 }
     | write Atom Atom Atom
                         { Write $2 $3 $4 $1 }

     | Exp2 '+...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '-...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '-' Exp2       { binOp $1 (L $2 (SYMBOL Minus [] (nameFromString "-"))) $3 }
     | Exp2 '*...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '*' Exp2       { binOp $1 (L $2 (SYMBOL Times [] (nameFromString "*"))) $3 }
     | Exp2 '/...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '%...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '//...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '%%...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '**...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '>>...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '>>>...' Exp2  { binOp $1 $2 $3 }
     | Exp2 '<<...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '&...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '|...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '&&...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '||...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '^...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '==...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '!=...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '<...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '<=...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '>...' Exp2    { binOp $1 $2 $3 }

     | Exp2 '>=' Exp2      { binOp $1 (L $2 (SYMBOL Geq [] (nameFromString ">="))) $3 }
     | Exp2 '>' Exp2       { binOp $1 (L $2 (SYMBOL Greater [] (nameFromString ">"))) $3 }
     | Exp2 '<=' Exp2      { binOp $1 (L $2 (SYMBOL Leq [] (nameFromString "<="))) $3 }
     | Exp2 '<' Exp2       { binOp $1 (L $2 (SYMBOL Less [] (nameFromString "<"))) $3 }

     | Apply
       { let (fname, args, loc) = $1 in Apply fname [ (arg, Observe) | arg <- args ] NoInfo loc }
     | Atom %prec juxtprec { $1 }

     | '-' Exp2
       { Negate $2 $1 }

     | Exp2 with '[' sepBy(DimIndex, ',') ']' '<-' Exp2
       { Update $1 $4 $7 (srclocOf $1) }


Apply :: { (QualName Name, [UncheckedExp], SrcLoc) }
      : Apply Atom %prec juxtprec
        { let (fname, args, loc) = $1 in (fname, args ++ [$2], loc) }
      | QualName Atom %prec juxtprec
        { (fst $1, [$2], snd $1) }
      | QualUnOpName Atom %prec juxtprec
        { (fst $1, [$2], snd $1) }

Atom :: { UncheckedExp }
Atom : PrimLit        { Literal (fst $1) (snd $1) }
     | stringlit      {% let L pos (STRINGLIT s) = $1 in do
                             s' <- mapM (getIntValue . fromIntegral . ord) s
                             t <- lift $ gets parserIntType
                             return $ ArrayLit (map (flip Literal pos . SignedValue) s') NoInfo pos }
     | empty '(' TypeExpDecl ')'   { Empty $3 $1 }
     | '(' Exp ')'                 { Parens $2 $1 }
     | '(' Exp ')[' sepBy(DimIndex, ',') ']' { Index (Parens $2 $1) $4 $1 }
     | '(' sepBy2(Exp, ',') ')'    { TupLit $2 $1 }
     | '('      ')'                { TupLit [] $1 }
     | '[' sepBy1(Exp, ',') ']'    { ArrayLit (fst $2:snd $2) NoInfo $1 }
     | QualVarSlice  { let (v,slice,loc) = $1
                       in Index (Var v NoInfo loc) slice loc }
     | QualName { Var (fst $1) NoInfo (snd $1) }
     | '#' FieldId Atom { Project (fst $2) $3 NoInfo $1 }
     | '{' sepBy(Field, ',') '}' { RecordLit $2 $1 }

Field :: { FieldBase NoInfo Name }
       : FieldId '=' Exp { RecordField (fst $1) $3 (snd $1) }
       | Exp             { RecordRecord $1 }

LetExp :: { UncheckedExp }
     : let Pattern '=' Exp LetBody
                      { LetPat $2 $4 $5 $1 }

     | let id many1(Param) maybeAscription(TypeExpDecl) '=' Exp LetBody
                      { let L _ (ID name) = $2
                        in LetFun name (fst $3 : snd $3, (fmap declaredType $4), NoInfo, $6) $7 $1 }

     | let VarSlice '=' Exp LetBody
                      { let (v,slice,loc) = $2; ident = Ident v NoInfo loc
                        in LetWith ident ident slice $4 $5 loc }

     | loop '(' Pattern ')' '=' LoopForm do Exp LetBody
                      {% liftM (\t -> DoLoop $3 t $6 $8 $9 $1)
                               (patternExp $3) }
     | loop '(' Pattern '=' Exp ')' '=' LoopForm do Exp LetBody
                  { DoLoop $3 $5 $8 $10 $11 $1 }

LetBody :: { UncheckedExp }
    : in Exp %prec letprec { $2 }
    | LetExp %prec letprec { $1 }

LoopForm : for VarId '<' Exp
           { For FromUpTo ZeroBound $2 $4 }
         | for Atom '<=' VarId '<' Exp
           { For FromUpTo (ExpBound $2) $4 $6 }
         | for Atom '>' VarId '>=' Exp
           { For FromDownTo (ExpBound $6) $4 $2 }
         | for Atom '>' VarId
           { For FromDownTo ZeroBound $4 $2 }
         | while Exp      { While $2 }

VarSlice :: { (Name, [UncheckedDimIndex], SrcLoc) }
          : 'id[' sepBy(DimIndex, ',') ']'
              { let L loc (INDEXING v) = $1
                in (v, $2, loc) }

QualVarSlice :: { (QualName Name, [UncheckedDimIndex], SrcLoc) }
              : VarSlice
                { let (x, y, z) = $1 in (QualName [] x, y, z) }
              | 'qid[' sepBy(DimIndex, ',') ']'
                { let L loc (QUALINDEXING qs v) = $1 in (QualName qs v, $2, loc) }

DimIndex :: { UncheckedDimIndex }
         : Exp2                   { DimFix $1 }
         | Exp2 ':' Exp2          { DimSlice (Just $1) (Just $3) Nothing }
         | Exp2 ':'               { DimSlice (Just $1) Nothing Nothing }
         |      ':' Exp2          { DimSlice Nothing (Just $2) Nothing }
         |      ':'               { DimSlice Nothing Nothing Nothing }
         | Exp2 ':' Exp2 ':' Exp2 { DimSlice (Just $1) (Just $3) (Just $5) }
         |      ':' Exp2 ':' Exp2 { DimSlice Nothing (Just $2) (Just $4) }
         | Exp2 ':'      ':' Exp2 { DimSlice (Just $1) Nothing (Just $4) }
         |      ':'      ':' Exp2 {  DimSlice Nothing Nothing (Just $3) }

VarId : id { let L pos (ID name) = $1 in Ident name NoInfo pos }

FieldId :: { (Name, SrcLoc) }
         : id     { let L loc (ID name) = $1 in (name, loc) }
         | declit { let L loc (DECLIT n) = $1 in (nameFromString (show n), loc) }

Pattern :: { PatternBase NoInfo Name }
Pattern : InnerPattern ':' TypeExpDecl { PatternAscription $1 $3 }
        | InnerPattern                 { $1 }

InnerPattern :: { PatternBase NoInfo Name }
InnerPattern : VarId                            { Id $1 }
             | '_'                              { Wildcard NoInfo $1 }
             | '(' ')'                          { TuplePattern [] $1 }
             | '(' Pattern ')'                  { PatternParens $2 $1 }
             | '(' sepBy2(Pattern, ',') ')'     { TuplePattern $2 $1 }
             | '{' sepBy(FieldPattern, ',') '}' { RecordPattern $2 $1 }

FieldPattern :: { (Name, PatternBase NoInfo Name) }
              : FieldId '=' Pattern     { (fst $1, $3) }
              | FieldId ':' TypeExpDecl { (fst $1,
                                           PatternAscription (Id $ Ident (fst $1) NoInfo (snd $1))
                                                             $3) }
              | FieldId                 { (fst $1, Id $ Ident (fst $1) NoInfo (snd $1)) }

maybeAscription(p) : ':' p { Just $2 }
                   |       { Nothing }

Curry : Curry Atom
        { let (fname, args, loc) = $1 in (fname, args ++ [$2], loc) }
      | QualName Atom %prec indexprec
        { (fst $1, [$2], snd $1) }

FunAbstr :: { UncheckedLambda }
         : '(' '\\' many1(Param) maybeAscription(TypeExpDecl) '->' Exp ')'
           { AnonymFun (fst $3 : snd $3) $6 $4 NoInfo $1 }
         | QualName
           { CurryFun (fst $1) [] NoInfo (snd $1) }
         | '(' QualUnOpName ')'
           { CurryFun (fst $2) [] NoInfo (snd $2) }
         | '(' Curry ')'
           { let (fname, args, loc) = $2 in CurryFun fname args NoInfo loc }
           -- Minus is handed explicitly here because I could not
           -- figure out how to resolve the ambiguity with negation.
         | '(' '-' Exp2 ')'
           { CurryBinOpRight (QualName [] (nameFromString "-")) $3 (NoInfo, NoInfo) NoInfo $1 }
         | '(' '-' ')'
           { BinOpFun (QualName [] (nameFromString "-")) NoInfo NoInfo NoInfo $1 }
         | '(' Exp2 '-' ')'
           { CurryBinOpLeft (QualName [] (nameFromString "-")) $2 (NoInfo, NoInfo) NoInfo (srclocOf $1) }
         | '(' BinOp Exp2 ')'
           { CurryBinOpRight $2 $3 (NoInfo, NoInfo) NoInfo $1 }
         | '(' Exp2 BinOp ')'
           { CurryBinOpLeft $3 $2 (NoInfo, NoInfo) NoInfo $1 }
         | '(' BinOp ')'
           { BinOpFun $2 NoInfo NoInfo NoInfo $1 }

Value : IntValue { $1 }
      | FloatValue { $1 }
      | StringValue { $1 }
      | BoolValue { $1 }
      | ArrayValue { $1 }

CatValues : many(Value) { $1 }

NaturalInt :: { Int }
           : declit { let L _ (DECLIT num) = $1 in fromIntegral num  }
           | intlit { let L _ (INTLIT num) = $1 in fromIntegral num  }

NaturalInts :: { [Int] }
           : NaturalInt                 { [$1] }
           | NaturalInt ',' NaturalInts { $1 : $3  }

PrimType :: { PrimType }
         : id {% let L _ (ID s) = $1 in primTypeFromName s }

IntValue :: { Value }
         : SignedLit { PrimValue (SignedValue (fst $1)) }
         | '-' SignedLit { PrimValue (SignedValue (intNegate (fst $2))) }
         | UnsignedLit { PrimValue (UnsignedValue (fst $1)) }

FloatValue :: { Value }
         : FloatLit { PrimValue (FloatValue (fst $1)) }
         | '-' FloatLit { PrimValue (FloatValue (floatNegate (fst $2))) }

StringValue : stringlit  {% let L pos (STRINGLIT s) = $1 in do
                             s' <- mapM (getIntValue . fromIntegral . ord) s
                             t <- lift $ gets parserIntType
                             return $ ArrayValue (arrayFromList $ map (PrimValue . SignedValue) s') $ Prim $ Signed t }
BoolValue : true           { PrimValue $ BoolValue True }
          | false          { PrimValue $ BoolValue False }

SignedLit :: { (IntValue, SrcLoc) }
          : i8lit   { let L pos (I8LIT num)  = $1 in (Int8Value num, pos) }
          | i16lit  { let L pos (I16LIT num) = $1 in (Int16Value num, pos) }
          | i32lit  { let L pos (I32LIT num) = $1 in (Int32Value num, pos) }
          | i64lit  { let L pos (I64LIT num) = $1 in (Int64Value num, pos) }
          | declit  {% let L pos (DECLIT num) = $1 in do num' <- getIntValue (toInteger num); return (num', pos) }
          | intlit  {% let L pos (INTLIT num) = $1 in do num' <- getIntValue (toInteger num); return (num', pos) }
          | charlit {% let L pos (CHARLIT char) = $1 in do
                       num <- getIntValue $ fromIntegral $ ord char
                       return (num, pos) }

UnsignedLit :: { (IntValue, SrcLoc) }
            : u8lit  { let L pos (U8LIT num)  = $1 in (Int8Value num, pos) }
            | u16lit { let L pos (U16LIT num) = $1 in (Int16Value num, pos) }
            | u32lit { let L pos (U32LIT num) = $1 in (Int32Value num, pos) }
            | u64lit { let L pos (U64LIT num) = $1 in (Int64Value num, pos) }

FloatLit :: { (FloatValue, SrcLoc) }
         : f32lit { let L pos (F32LIT num) = $1 in (Float32Value num, pos) }
         | f64lit { let L pos (F64LIT num) = $1 in (Float64Value num, pos) }
         | reallit {% let L pos (REALLIT num) = $1 in do num' <- getRealValue num; return (num', pos) }

PrimLit :: { (PrimValue, SrcLoc) }
        : SignedLit { let (x,loc) = $1 in (SignedValue x, loc) }
        | UnsignedLit { let (x,loc) = $1 in (UnsignedValue x, loc) }
        | FloatLit { let (x,loc) = $1 in (FloatValue x, loc) }

        | true   { (BoolValue True, $1) }
        | false  { (BoolValue False, $1) }

ArrayValue :  '[' Value ']'
             {% return $ ArrayValue (arrayFromList [$2]) $ toStruct $ valueType $2
             }
           |  '[' Value ',' Values ']'
             {% case combArrayTypes (valueType $2) $ map valueType $4 of
                  Nothing -> throwError "Invalid array value"
                  Just ts -> return $ ArrayValue (arrayFromList $ $2:$4) ts
             }
           | empty '(' PrimType ')'
             { ArrayValue (listArray (0,-1) []) (Prim $3) }

Values : Value ',' Values { $1 : $3 }
       | Value            { [$1] }
       |                  { [] }

{

reverseNonempty :: (a, [a]) -> (a, [a])
reverseNonempty (x, l) =
  case reverse (x:l) of
    x':rest -> (x', rest)
    []      -> (x, [])

data ParserEnv = ParserEnv {
                 parserFile :: FilePath
               , parserIntType :: IntType
               , parserRealType :: FloatType
               , parserRealFun :: Double -> FloatValue
               }

newParserEnv :: FilePath -> IntType -> FloatType -> ParserEnv
newParserEnv path intType realType =
  let s = ParserEnv path intType realType Float64Value
  in modParserEnv s realType

modParserEnv :: ParserEnv -> FloatType -> ParserEnv
modParserEnv s realType =
  case realType of
    Float32 -> s {
        parserRealType = Float32,
        parserRealFun = float32RealFun
      }
    Float64 -> s {
        parserRealType = Float64,
        parserRealFun = float64RealFun
      }
  where

    float32RealFun x =
      let (m,n) = decodeFloat x
      in Float32Value $ encodeFloat m n
    float64RealFun = Float64Value

type ParserMonad a =
  ExceptT String (
    StateT ParserEnv (
       StateT [L Token] ReadLineMonad)) a

data ReadLineMonad a = Value a
                     | GetLine (T.Text -> ReadLineMonad a)

readLineFromMonad :: ReadLineMonad T.Text
readLineFromMonad = GetLine Value

instance Monad ReadLineMonad where
  return = Value
  Value x >>= f = f x
  GetLine g >>= f = GetLine $ \s -> g s >>= f

instance Functor ReadLineMonad where
  f `fmap` m = do x <- m
                  return $ f x

instance Applicative ReadLineMonad where
  (<*>) = ap

getLinesFromIO :: ReadLineMonad a -> IO a
getLinesFromIO (Value x) = return x
getLinesFromIO (GetLine f) = do
  s <- T.getLine
  getLinesFromIO $ f s

getLinesFromTexts :: [T.Text] -> ReadLineMonad a -> Either String a
getLinesFromTexts _ (Value x) = Right x
getLinesFromTexts (x : xs) (GetLine f) = getLinesFromTexts xs $ f x
getLinesFromTexts [] (GetLine _) = Left "Ran out of input"

getNoLines :: ReadLineMonad a -> Either String a
getNoLines (Value x) = Right x
getNoLines (GetLine _) = Left "Unexpected end of input"

combArrayTypes :: TypeBase Rank ()
               -> [TypeBase Rank ()]
               -> Maybe (TypeBase Rank ())
combArrayTypes t ts = foldM comb t ts
  where comb x y
          | x == y    = Just x
          | otherwise = Nothing

arrayFromList :: [a] -> Array Int a
arrayFromList l = listArray (0, length l-1) l

patternExp :: UncheckedPattern -> ParserMonad UncheckedExp
patternExp (Id ident) = return $ Var (QualName [] (identName ident)) NoInfo $ srclocOf ident
patternExp (TuplePattern pats loc) = TupLit <$> (mapM patternExp pats) <*> return loc
patternExp (Wildcard _ loc) = throwError $ "Cannot have wildcard at " ++ locStr loc

eof :: L Token
eof = L (SrcLoc $ Loc (Pos "" 0 0 0) (Pos "" 0 0 0)) EOF

binOpName (L _ (SYMBOL _ qs op)) = QualName qs op

binOp x (L loc (SYMBOL _ qs op)) y =
  BinOp (QualName qs op) (x, Observe) (y, Observe) NoInfo loc

getTokens :: ParserMonad [L Token]
getTokens = lift $ lift get

putTokens :: [L Token] -> ParserMonad ()
putTokens ts = lift $ lift $ put ts

primTypeFromName :: Name -> ParserMonad PrimType
primTypeFromName s = maybe boom return $ HM.lookup s namesToPrimTypes
  where boom = fail $ "No type named " ++ nameToString s

defaultType :: Name -> ParserMonad ()
defaultType name = do
  t <- primTypeFromName name
  s <- lift get
  case t of
    Signed t'    -> lift $ put s { parserIntType = t' }
    Unsigned t'  -> lift $ put s { parserIntType = t' }
    FloatType t' -> lift $ put $ modParserEnv s t'
    _            -> fail $ "Cannot default literals to type " ++ pretty name

getFilename :: ParserMonad FilePath
getFilename = lift $ gets parserFile

getIntValue :: Integer -> ParserMonad IntValue
getIntValue x = do
  t <- lift $ gets parserIntType
  return $ getIntFun t x

getIntFun :: IntType -> (Integer -> IntValue)
getIntFun Int8  = Int8Value . fromInteger
getIntFun Int16 = Int16Value . fromInteger
getIntFun Int32 = Int32Value . fromInteger
getIntFun Int64 = Int64Value . fromInteger

getRealValue :: Double -> ParserMonad FloatValue
getRealValue x = do f <- lift $ gets parserRealFun
                    return $ f x

intNegate :: IntValue -> IntValue
intNegate (Int8Value v) = Int8Value (-v)
intNegate (Int16Value v) = Int16Value (-v)
intNegate (Int32Value v) = Int32Value (-v)
intNegate (Int64Value v) = Int64Value (-v)

floatNegate :: FloatValue -> FloatValue
floatNegate (Float32Value v) = Float32Value (-v)
floatNegate (Float64Value v) = Float64Value (-v)

readLine :: ParserMonad T.Text
readLine = lift $ lift $ lift readLineFromMonad

lexer :: (L Token -> ParserMonad a) -> ParserMonad a
lexer cont = do
  ts <- getTokens
  case ts of
    [] -> do
      ended <- lift $ runExceptT $ cont eof
      case ended of
        Right x -> return x
        Left _ -> do
          ts' <- scanTokens <$> getFilename <*> readLine
          ts'' <- case ts' of Right x -> return x
                              Left e  -> throwError e
          case ts'' of
            [] -> cont eof
            xs -> do
              putTokens xs
              lexer cont
    (x : xs) -> do
      putTokens xs
      cont x

parseError :: L Token -> ParserMonad a
parseError (L _ EOF) = throwError "Parse error: End of file"
parseError tok       = throwError $ "Parse error at " ++ locStr (srclocOf tok)

--- Now for the parser interface.

-- | A parse error.  Use 'show' to get a human-readable description.
data ParseError = ParseError String

instance Show ParseError where
  show (ParseError s) = s

parseInMonad :: ParserMonad a -> FilePath -> T.Text
             -> ReadLineMonad (Either ParseError a)
parseInMonad p file program =
  either (Left . ParseError) Right <$> either (return . Left)
  (evalStateT (evalStateT (runExceptT p) env))
  (scanTokens file program)
  where env = newParserEnv file Int32 Float64

parseIncrementalIO :: ParserMonad a -> FilePath -> T.Text
                   -> IO (Either ParseError a)
parseIncrementalIO p file program =
  getLinesFromIO $ parseInMonad p file program

parseIncremental :: ParserMonad a -> FilePath -> T.Text
                 -> Either ParseError a
parseIncremental p file program =
  either (Left . ParseError) id
  $ getLinesFromTexts (T.lines program)
  $ parseInMonad p file mempty

parse :: ParserMonad a -> FilePath -> T.Text
      -> Either ParseError a
parse p file program =
  either (Left . ParseError) id
  $ getNoLines $ parseInMonad p file program

-- | Parse an Futhark expression greedily from the given 'String', only parsing
-- enough lines to get a correct expression, using the 'FilePath' as the source
-- name for error messages.
parseExpIncr :: FilePath -> T.Text
             -> Either ParseError UncheckedExp
parseExpIncr = parseIncremental expression

-- | Parse an Futhark expression incrementally from IO 'getLine' calls, using the
-- 'FilePath' as the source name for error messages.
parseExpIncrIO :: FilePath -> T.Text
               -> IO (Either ParseError UncheckedExp)
parseExpIncrIO = parseIncrementalIO expression

}
