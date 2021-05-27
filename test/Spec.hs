{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE DataKinds #-}
import HList
import Data.Proxy ( Proxy(Proxy) )

testList :: HList '[HList '[Int, Int], HList '[Char]]
testList = (1 :|| 2 :|| HEmpty) :|| ('a' :|| HEmpty) :|| HEmpty

testListConcat :: HList '[Int, Int, Char]
testListConcat = hetConcat (Proxy @'[ '[Int, Int], '[Char] ]) testList

