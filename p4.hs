import Cp
import Nat
data FTree a c = Unit c | Comp a (FTree a c) (FTree a c) deriving Show

inFTree = either Unit (tripleUncurry Comp)

tripleUncurry :: (a -> b -> c -> d) -> (a,(b,c)) -> d
tripleUncurry f (a,(b,c)) = f a b c
outFTree (Unit a)= i1 a
outFTree (Comp a t1 t2) = i2 (a, (t1,t2))

cataFTree a = a . (recFTree (cataFTree a)) . outFTree
anaFTree f = inFTree . (recFTree (anaFTree f) ) . f
hyloFTree a c = cataFTree a . anaFTree c
baseFTree f g h  = g -|- (f  >< (h >< h))
recFTree f = baseFTree id id f

generatePTree = anaFTree (seed.(outNat >< id)) .  split id (const 1)
               where
                 cenas x = ((sqrt 2) / 2 * x)
                 seed ((Left()), x ) = Left (x)
                 seed (Right c, x) = Right (x, ((c, cenas x), (c, cenas x)))
