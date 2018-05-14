{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module Conversions where
import Data.List
import Data.Maybe
import qualified Data.Map as Map

type Symbol = Char
type Alphabet = [Symbol]
type Language = [String]

newtype DFA a = DFA ([a], Alphabet, Map.Map (a,Symbol) a  , a, [a])
newtype NFA a = NFA ([a], Alphabet, Map.Map (a,Symbol) [a], a, [a])  
  
class (Ord state, Ord mapsTo) => Automaton a state mapsTo | a -> state, a -> mapsTo where
  states    :: a -> [state]
  sigma     :: a -> Alphabet
  delta     :: a -> Map.Map (state,Symbol) mapsTo
  initial   :: a -> state
  final     :: a -> [state]
  
  valid     :: a -> Bool
  consume   :: a -> [state] -> Symbol -> [state]
  reachable :: a -> [state] -> String -> [state] 
  accepts   :: a -> String -> Bool
  
  language  :: a -> Language
  language fa = filter (accepts fa) (kleeneStar (sigma fa))
  
  accessibleStates :: a -> [state]
  accessibleStates fa = cover (\x -> concat [reachable fa x (symbol:"") | symbol <- sigma fa]) [initial fa]  
  
-- epsilon, reserved for empty transitions
-- epsilon itself isn't rendered by show, so @ will have to do
eps :: Symbol
eps = '@'

-- Formatting

listFormat :: (Show a) => [a] -> String
listFormat = intercalate " | " . map show

tupleFormat :: (Show a, Show b, Show c) => ((a,b), c) -> String
tupleFormat ((x,y),z) = show x ++ " ~~" ++ show y ++ "~> " ++ show z

mapFormat :: (Show a, Show b, Show c) => Map.Map (a,b) c -> String
mapFormat = intercalate "\n            " . map tupleFormat . Map.toList

automatonFormat :: (Show a, Show b, Show c, Show d) => 
                    ([a], [Symbol], Map.Map (b,c) d, a, [a]) -> String
automatonFormat (q,s,d,i,f) = "States Q  : " ++ listFormat q ++ "\n" ++
                              "Sigma     : " ++ listFormat s ++ "\n" ++
                              "Delta     : " ++ mapFormat d ++ "\n" ++
                              "Initial I : " ++ show i ++ "\n" ++
                              "Final F   : " ++ listFormat f ++ "\n"

-- Syntactic sugar

(~>) :: a -> b -> (a,b)
a ~> b = (a,b)
   
-- 'Set' operations
       
sublist :: (Eq a) => [a] -> [a] -> Bool
sublist l l' = all (`elem` l') l

coextensive :: (Eq a) => [a] -> [a] -> Bool
coextensive l l' = l `sublist` l' && l' `sublist` l

cover :: Eq a => ([a] -> [a]) -> [a] -> [a]
cover f x = let y = nub (x ++ f x) in if length x == length y then x else cover f y

cart :: [a] -> [b] -> [(a,b)]
cart xs ys = [(x,y) | x <- xs, y <- ys]

-- Alphabet & language operations

kleeneStar :: Alphabet -> Language
kleeneStar alphabet = "" : extend [""]
  where extend prev = let curr = [s:x | s <- alphabet, x <- prev]
                      in curr ++ extend curr
                      
kleenePlus :: Alphabet -> Language                       
kleenePlus = tail . kleeneStar

concatenate :: Language -> Language -> Language
concatenate l1 l2 = [x ++ y | x <- l1, y <- l2]

ln :: Language -> Int -> Language
ln l 0 = [""]
ln l 1 = l
ln l n = concatenate l (ln l (pred n))

starClosure :: Language -> Language
starClosure l = concat [ln l n | n <- [0..]]

posClosure :: Language -> Language
posClosure l = tail $ starClosure l

-------------------------------------
-- Deterministic finite automata
-------------------------------------

-- linz figure 2.1
dfa1 :: DFA Int
dfa1 = DFA ([0,1,2], ['0','1'], t, 0, [1])
  where t = Map.fromList [(0,'0') ~> 0,  (0,'1') ~> 1,
                          (1,'0') ~> 0,  (1,'1') ~> 2,
                          (2,'0') ~> 2,  (2,'1') ~> 1
                         ]
                         
-- linz figure 2.18
dfa2 :: DFA Int
dfa2 = DFA ([0..4], ['0','1'], t, 0, [2,4])
  where t = Map.fromList [(0,'0') ~> 1,  (0,'1') ~> 3,
                          (1,'0') ~> 2,  (1,'1') ~> 4,
                          (2,'0') ~> 1,  (2,'1') ~> 4,
                          (3,'0') ~> 2,  (3,'1') ~> 4,
                          (4,'0') ~> 4,  (4,'1') ~> 4]

instance (Ord a) => Automaton (DFA a) a a where
  states  (DFA (q,_,_,_,_)) = q
  sigma   (DFA (_,s,_,_,_)) = s
  delta   (DFA (_,_,d,_,_)) = d
  initial (DFA (_,_,_,i,_)) = i
  final   (DFA (_,_,_,_,f)) = f
     
  valid (DFA (q,s,d,i,f)) = 
    coextensive (Map.keys d) domain &&
    Map.elems d `sublist` q &&
    i `elem` q &&
    f `sublist` q &&
    eps `notElem` s
      where domain = cart q s 
  
  consume dfa at x = nub [let Just to = Map.lookup (y,x) (delta dfa) in to | y <- at]
      
  reachable _   at []     = at
  reachable dfa at (x:xs) = reachable dfa (consume dfa at x) xs

  accepts dfa s = head (reachable dfa [initial dfa] s) `elem` final dfa

instance (Show a) => Show (DFA a) where
  show (DFA dfa) = "--> DFA\n" ++ 
                   automatonFormat dfa

relabelDFA :: (Ord a, Ord b) => DFA a -> [b] -> DFA b
relabelDFA (DFA (q,s,d,i,f)) pickFrom = DFA (q',s,d',i',f')
  where stateMap = zip q pickFrom
        q' = map snd stateMap
        d' = relabelDelta
        i' = let Just x = lookup i stateMap in x
        f' = [let Just x = lookup y stateMap in x | y <- f]
        relabelDelta = Map.fromList $ zip (map (\(st,sym) -> let Just st' = lookup st stateMap in (st', sym)) (Map.keys d))
                                          (map (\x -> let Just y = lookup x stateMap in y) (Map.elems d)) 

---------------------------------------
-- Nondeterministic finite automata
---------------------------------------

-- linz figure 2.9 
nfa1 :: NFA Int
nfa1 = NFA ([0,1,2], ['0','1'], t, 0, [0])
  where t = Map.fromList [(0, eps) ~> [2]  ,  (0, '1') ~> [1],
                          (1, '0') ~> [0,2],  (1, '1') ~> [2]
                         ]

-- linz figure 2.12 
nfa2 :: NFA Int
nfa2 = NFA ([0,1,2], ['a','b'], t, 0, [1])
  where t = Map.fromList [(0, 'a') ~> [1],
                          (1, 'a') ~> [1],  (1, eps) ~> [2],
                          (2, 'b') ~> [0]
                         ]
                         
-- linz figure 2.14
nfa3 :: NFA Int
nfa3 = NFA ([0,1,2], ['0','1'], t, 0, [1])
  where t = Map.fromList [(0, '0') ~> [0,1], (0,'1') ~> [1],
                          (1, '0') ~> [2],   (1, '1') ~> [2],
                          (2, '1') ~> [2]
                         ]
                         
instance (Ord a) => Automaton (NFA a) a [a] where
  states  (NFA (q,_,_,_,_)) = q
  sigma   (NFA (_,s,_,_,_)) = s
  delta   (NFA (_,_,d,_,_)) = d
  initial (NFA (_,_,_,i,_)) = i
  final   (NFA (_,_,_,_,f)) = f
  
  valid (NFA (q,s,d,i,f)) = 
    Map.keys d `sublist` domain &&
    all (`sublist` q) (Map.elems d) &&
    i `elem` q &&
    f `sublist` q &&
    eps `notElem` s
    where domain = cart q (eps:s)
  
  consume nfa at x = nub $ concat [fromMaybe [] (Map.lookup (s,x) (delta nfa)) | s <- at]
  
  reachable _   at []     = at
  reachable nfa at (x:xs) = if   null at then []
                            else reachable nfa (consumeClosure nfa at x) xs

  accepts nfa s = let canReach = reachable nfa (epsilonReachable nfa [initial nfa]) s
                  in  any (`elem` final nfa) canReach
                     
instance (Show a) => Show (NFA a) where
  show (NFA nfa) = "--> NFA\n" ++ 
                   automatonFormat nfa

epsilonReachable :: (Ord a) => NFA a -> [a] -> [a]
epsilonReachable nfa = cover (\x -> consume nfa x eps)

consumeClosure :: (Ord a) => NFA a -> [a] -> Symbol -> [a]
consumeClosure nfa at x =
  nub $ epsilonReachable nfa $ consume nfa (epsilonReachable nfa at) x

relabelNFA :: (Ord a, Ord b) => NFA a -> [b] -> NFA b
relabelNFA (NFA (q,s,d,i,f)) pickFrom = NFA (q',s,d',i',f')
  where stateMap = zip q pickFrom
        q' = map snd stateMap
        d' = relabelDelta
        i' = let Just x = lookup i stateMap in x
        f' = [let Just x = lookup y stateMap in x | y <- f]
        relabelDelta = Map.fromList $ zip (map (\(st,sym) -> let Just st' = lookup st stateMap in (st', sym)) (Map.keys d))
                                          (map (\l -> [let Just x = lookup y stateMap in x | y <- l] ) (Map.elems d)) 

-- nfa2dfa

getMissingTransition :: (Ord a) => DFA a -> Maybe (a,Symbol)
getMissingTransition dfa =
  let missing = reqTransitions \\ Map.keys (delta dfa)
  in  if null missing then Nothing else Just (head missing)
  where reqTransitions = [(s,x) | s <- states dfa, x <- sigma dfa]

nfa2dfa :: (Ord a) => NFA a -> DFA [a]
nfa2dfa nfa = complete (DFA ([[initial nfa]], sigma nfa, Map.empty, [initial nfa], []))
  where complete dfa@(DFA (q,s,d,i,[])) = 
          let toAdd = getMissingTransition dfa
          in case toAdd of
            Just (state,symbol) -> 
              let target = consumeClosure nfa state symbol
              in  let existing = filter (coextensive target) q
                  in  complete $ DFA $ 
                        if null existing
                        then (target:q, s, Map.insert (state,symbol) target d         , i, [])
                        else (q       , s, Map.insert (state,symbol) (head existing) d, i, [])
            Nothing -> 
              let f = filter (any (`elem` final nfa)) q
              in  DFA $ if any (`elem` final nfa) (epsilonReachable nfa i)
                        then (q, s, d, i, i:f)
                        else (q, s, d, i, f  )
                       
-- distinguishability & reduction

removeInaccessible :: Ord a => DFA a -> DFA a
removeInaccessible dfa@(DFA (q,s,d,i,f)) = 
  DFA (accessible,s,d',i,f')
  where accessible = accessibleStates dfa
        f' = f `intersect` accessible
        d' = Map.fromList $ filter (\((x,y),z) -> x `elem` accessible && z `elem` accessible) (Map.toList d)
   
mark :: Ord a => DFA a -> [(a,a)]
mark dfa@(DFA (q,s,d,i,f)) = cover ext distinguishable
  where ext marked = [(x,y) | (x,y) <- cart q q, sym <- s,
                              (head (consume dfa [x] sym), head (consume dfa [y] sym)) `elem` marked]
        distinguishable = cart (q \\ f) f ++ cart f (q \\ f)

equivClasses dfa = nub $ generateEquiv (states dfa)
  where indist = cart (states dfa) (states dfa) \\ mark dfa
        generateEquiv = map (\x -> map snd (filter ((==) x . fst) indist))  

minimize :: Ord a => DFA a -> DFA [a]
minimize dfa@(DFA (q,s,d,i,f)) = DFA (q',s,d',i',f')
  where q' = equivClasses dfa
        i' = head $ filter (i `elem`) q'
        d' = Map.fromList $ nub $ buildTable $ Map.toList d
        buildTable [] = []
        buildTable (((a,b),c) : xs) = ((head (filter (a `elem`) q'), b), head (filter (c `elem`) q')) : buildTable xs
        f' = filter (not . null . intersect f) q'

--------------------------
-- Regular expressions
--------------------------

data Regex = Empty | Eps | S Symbol | 
             Plus Regex Regex | Dot Regex Regex | Star Regex
  deriving (Eq, Ord)
instance Show Regex where
  show Empty        = "{}"
  show Eps          = "@"
  show (S c)        = "(" ++ (c : "") ++ ")"
  show (Plus r1 r2) = "(" ++ show r1 ++ " + " ++ show r2 ++ ")"
  show (Dot  r1 r2) = "(" ++ show r1 ++ show r2 ++ ")"
  show (Star r1)    = show r1 ++ "*"
  
regex1 :: Regex
regex1 = Dot left right
  where left  = Star (Plus sa (Dot sb sb))
        right = Plus (Dot sb (Star sa)) Eps
        sa = S 'a'
        sb = S 'b'

lang :: Regex -> Language
lang Empty        = []
lang Eps          = [""]
lang (S c)        = [c:""]
lang (Plus r1 r2) = lang r1 ++ lang r2
lang (Dot r1 r2)  = concatenate (lang r1) (lang r2)
lang (Star r1)    = starClosure (lang r1)

-- regex2nfa, regex2dfa

regex2nfa :: Regex -> NFA Int
regex2nfa Empty        = NFA ([0,1], [],  Map.empty                     , 0, [1])
regex2nfa Eps          = NFA ([0,1], [],  Map.fromList [(0, eps) ~> [1]], 0, [1])
regex2nfa (S c)        = NFA ([0,1], [c], Map.fromList [(0,  c ) ~> [1]], 0, [1])
regex2nfa (Plus r1 r2) =
  NFA (q,s,d,i,[f])
    where nfaR1 = regex2nfa r1
          nfaR2 = let min = maximum (states nfaR1) + 1
                  in  relabelNFA (regex2nfa r2) [min..]
          max = maximum (states nfaR2)
          i = max+1
          f = max+2
          q = [i,f] ++ states nfaR1 ++ states nfaR2
          s = nub $ sigma nfaR1 ++ sigma nfaR2
          finalTargetsR1 = let x = Map.lookup (head (final nfaR1), eps) (delta nfaR1) 
                           in  fromMaybe [] x
          finalTargetsR2 = let x = Map.lookup (head (final nfaR2), eps) (delta nfaR2)
                           in  fromMaybe [] x
          d = let existing = Map.union (delta nfaR1) (delta nfaR2)
              in Map.fromList $
                  Map.toList existing ++ 
                  [(i, eps)                  ~> [initial nfaR1, initial nfaR2],
                   (head (final nfaR1), eps) ~> (f:finalTargetsR1),
                   (head (final nfaR2), eps) ~> (f:finalTargetsR2)
                  ]
regex2nfa (Dot r1 r2) = 
  NFA (q,s,d,i,[f])
    where nfaR1 = regex2nfa r1
          nfaR2 = let min = maximum (states nfaR1) + 1
                  in relabelNFA (regex2nfa r2) [min..]
          max = maximum (states nfaR2)
          i = max+1
          f = max+2
          q = [i,f] ++ states nfaR1 ++ states nfaR2
          s = nub $ sigma nfaR1 ++ sigma nfaR2
          finalTargetsR1 = let x = Map.lookup (head (final nfaR1), eps) (delta nfaR1)
                           in  fromMaybe [] x
          finalTargetsR2 = let x = Map.lookup (head (final nfaR2), eps) (delta nfaR2)
                           in  fromMaybe [] x
          d = let existing = Map.union (delta nfaR1) (delta nfaR2)
              in Map.fromList $
                   Map.toList existing ++ 
                   [(i, eps)                  ~> [initial nfaR1],
                    (head (final nfaR1), eps) ~> (initial nfaR2:finalTargetsR1),
                    (head (final nfaR2), eps) ~> (f:finalTargetsR2)
                   ]
regex2nfa (Star r1) = 
  NFA (q,s,d,i,[f])
    where nfaR1 = regex2nfa r1
          max = maximum (states nfaR1)
          i = max+1
          f = max+2
          q = [i,f] ++ states nfaR1
          s = sigma nfaR1
          finalTargetsR1 = let x = Map.lookup (head (final nfaR1), eps) (delta nfaR1)
                           in  fromMaybe [] x
          d = Map.fromList $
              Map.toList (delta nfaR1) ++ 
                  [(i, eps)                  ~> [initial nfaR1, f],
                   (head (final nfaR1), eps) ~> (f:finalTargetsR1),
                   (f, eps)                  ~> [i]
                  ]

regex2dfa :: Regex -> DFA Int               
regex2dfa = (\x -> relabelDFA x [0..]) . minimize . nfa2dfa . regex2nfa

-------------------------------------------------------------
-- Generalized transition graphs
-------------------------------------------------------------

newtype GTG a = GTG ([a], Map.Map (a, a) Regex, a, [a])

-- Unfinished
gtgFormat :: (Show a) => 
                    ([a], Map.Map (a,a) Regex, a, [a]) -> String
gtgFormat (q,d,i,f) = "States Q  : " ++ listFormat q ++ "\n" ++
                   --   "Delta     : " ++ mapFormat d ++ "\n" ++
                      "Initial I : " ++ show i ++ "\n" ++
                      "Final F   : " ++ listFormat f ++ "\n"


instance (Show a) => Show (GTG a) where
  show (GTG gtg) = "--> GTG\n" ++ 
                   gtgFormat gtg

buildPlus :: [Symbol] -> Regex
buildPlus [] = Empty
buildPlus [x] = S x
buildPlus (x:y:xs) =  Plus (S x) (buildPlus (y:xs))

generalizedGTGTransitions :: Ord a => [a] -> [((a,Symbol), [a])] -> Map.Map (a, a) Regex
generalizedGTGTransitions q d = Map.fromList $ map makeTransition (cart q q)
  where makeTransition (x,y) = ((x, y), symbols x y)
        symbols x y = let xySymbols = map (snd . fst) $ filter (\((a,b),c) -> a == x && y `elem` c) d
                      in  buildPlus xySymbols
            
nfa2gtg :: Ord a => NFA a -> GTG a
nfa2gtg nfa@(NFA (q,s,d,i,f)) = GTG (q, d', i, f)
  where d' = generalizedGTGTransitions q (Map.toList d)

-- for when finding a result is certain
lookup' :: Ord a => a -> Map.Map a b -> b
lookup' x m = let Just result = Map.lookup x m in result

step3 :: Ord a => GTG a -> Regex
step3 gtg@(GTG (q,d,i,f)) = Dot t1 (Dot t2 t3)
  where j = head f
        t1 = Star $ lookup' (i,i) d
        t2 = lookup' (i,j) d
        t3 = Star $ Plus (lookup' (j,j) d) t3right
        t3right = Dot (lookup' (j,i) d) (Dot (Star (lookup' (i,i) d)) (lookup' (i,j) d))

-- r and s are kept, k is removed
step4 :: Ord a => GTG a -> a -> a -> a -> GTG a
step4 gtg@(GTG (q,d,i,f)) r s k =
  GTG (q',d',i,f')
  where q' = delete k q
        f' = delete k f
        d' = Map.insert (r,r) (term r r) $
             Map.insert (r,s) (term r s) $
             Map.insert (s,r) (term s r) $
             Map.insert (s,s) (term s s) $
             Map.delete (k,k) $
             Map.delete (r,k) $
             Map.delete (k,r) $
             Map.delete (s,k) $
             Map.delete (k,s) d
        term x y  = Plus (left x y) (right x y)
        left x y  = lookup' (x,y) d
        right x y = Dot (lookup' (x,k) d) (Dot (Star (lookup' (k,k) d)) (lookup' (k,y) d))

-- unfinished
steps3To5 :: Ord a => GTG a -> Regex
steps3To5 gtg@(GTG (q,d,i,f))
  | length q == 2 = step3 gtg
  | length q == 3 = steps3To5 $ step4 gtg i (head f) (head (q \\ [i, head f]))
  | otherwise     = undefined
  where k = if   length f > 1 then head f
            else head $ delete i (q \\ f)
