module Scratch where

-- based on https://hackage.haskell.org/package/extra-1.7.10/docs/Data-List-Extra.html

repeatedly :: (a -> [a] -> (b, [a])) -> [a] -> [b]
repeatedly f [] = []
repeatedly f (a:as) = b : repeatedly f as'
    where (b, as') = f a as

wordsBy :: (a -> Bool) -> [a] -> [[a]]
wordsBy f s = case dropWhile f s of
    [] -> []
    x:xs -> (x:w) : wordsBy f (drop 1 z)
        where (w,z) = break f xs

rle :: Eq a => [a] -> [(Int,a)]
rle = repeatedly process
  where process a as =
          let (p,s) = span (== a) as in
            ((1 + length p, a),s)

chunksOf :: Int -> [a] -> [[a]]
chunksOf i xs | i <= 0 = []
chunksOf i xs = repeatedly (\ x xs -> splitAt i (x:xs)) xs            