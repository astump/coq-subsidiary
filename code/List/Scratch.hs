module Scratch where

-- based on https://hackage.haskell.org/package/extra-1.7.10/docs/Data-List-Extra.html

mapThrough :: (a -> [a] -> (b, [a])) -> [a] -> [b]
mapThrough f [] = []
mapThrough f (a:as) = b : mapThrough f as'
    where (b, as') = f a as

wordsBy :: (a -> Bool) -> [a] -> [[a]]
wordsBy f s = case dropWhile f s of
    [] -> []
    x:xs -> (x:w) : wordsBy f (drop 1 z)
        where (w,z) = break f xs

wordsBy' :: (a -> Bool) -> [a] -> [[a]]
wordsBy' p [] = []
wordsBy' p (hd:tl) =
  if p hd
  then wordsBy' p tl 
  else let (w,z) = break p tl in
        (hd:w) : wordsBy' p z

rle :: Eq a => [a] -> [(Int,a)]
rle = mapThrough compressSpan
  where compressSpan a as =
          let (p,s) = span (== a) as in
            ((1 + length p, a),s)

chunksOf :: Int -> [a] -> [[a]]
chunksOf i xs | i <= 0 = []
chunksOf i xs = mapThrough (\ x xs -> splitAt i (x:xs)) xs            