{-# LANGUAGE ScopedTypeVariables  #-}
import qualified Data.ByteString.Lazy as B
import Data.Aeson
import IR

main = do
  Just (p :: Pipeline) <- decode <$> B.getContents
  B.putStr $ encode p
