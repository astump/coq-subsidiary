module Examples where

span' :: (a -> Bool) -> [a] -> ([a],[a])
span' _ []    =  ([], [])
span' p (x:xs) = if p x then
                   let (ys,zs) = span' p xs in (x:ys,zs)
                 else
                   ([],x:xs)

wordsBy :: (a -> Bool) -> [a] -> [[a]]
wordsBy p [] = []
wordsBy p (hd:tl) =
  if p hd
  then wordsBy p tl 
  else let (w,z) = span (not . p) tl in
        (hd:w) : wordsBy p z
