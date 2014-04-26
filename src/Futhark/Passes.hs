module Futhark.Passes
  ( CompileError(..)
  , FutharkM
  , compileError
  , Pass(..)
  , canFail
  , fotransform
  , uttransform
  , eotransform
  , hotransform
  , inlinetransform
  , splitasserttransform
  )
where

import Futhark.EnablingOpts.EnablingOptDriver
import Futhark.HOTrans.HOTransDriver
import qualified Futhark.FirstOrderTransform as FOT
import Futhark.Untrace
import Futhark.SplitAssertions
import Futhark.Pipeline

fotransform :: Pass
fotransform = Pass { passName = "first-order transform"
                   , passOp = return . FOT.transformProg
                   }

uttransform :: Pass
uttransform = Pass { passName = "debugging annotation removal"
                   , passOp = return . untraceProg
                   }

eotransform :: Pass
eotransform = Pass { passName = "enabling optimations"
                   , passOp = liftPass enablingOpts
                   }

hotransform :: Pass
hotransform = Pass { passName = "higher-order optimisations"
                   , passOp = liftPass highOrdTransf
                   }

inlinetransform :: Pass
inlinetransform = Pass { passName = "inline functions"
                      , passOp = liftPass aggInlineDriver
                      }

splitasserttransform :: Pass
splitasserttransform = Pass { passName = "split certificates"
                            , passOp = return . splitAssertions
                            }
