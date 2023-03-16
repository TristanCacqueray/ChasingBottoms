-- |
-- Module      :  Test.ChasingBottoms.IsType
-- Copyright   :  (c) Nils Anders Danielsson 2004-2022
-- License     :  See the file LICENCE.
--
-- Maintainer  :  http://www.cse.chalmers.se/~nad/
-- Stability   :  experimental
-- Portability :  non-portable (GHC-specific)
--
-- Internal helper functions.

module Test.ChasingBottoms.IsType
  ( isFunction
  , isTuple
  , isList
  , isString
  ) where

import Data.List
import Data.Typeable

-- | '@isFunction@ f' returns 'True' iff the top level \"constructor\"
-- of @f@ is a function arrow.
isFunction :: Typeable a => a -> Bool
isFunction f = con f == con not  -- TyCon is abstract.

con :: Typeable a => a -> TyCon
con = typeRepTyCon . typeOf

-- | This function is rather fragile, but should be OK. It is only
-- used by "Test.ChasingBottoms.ApproxShow", which should only be used
-- for debugging purposes anyway. The unit type is not considered to
-- be a tuple.
isTuple :: Typeable a => a -> Bool
isTuple x = "(," `isPrefixOf` show (con x)

isString :: Typeable a => a -> Bool
isString x = isList x && typeRepArgs (typeOf x) == typeRepArgs (typeOf "")

isList :: Typeable a => a -> Bool
isList x = con x == con ""
