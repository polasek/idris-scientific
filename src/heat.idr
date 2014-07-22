-- For simplicity, now only have extents of time and space in (0,eT) and (0,eX) respectively
-- Should probably do this in fractions, which would allow us to bound the range of t and x.
--approx : (dT : Real) -> (dX : Real) -> (eT : Real) -> (eX : Real) -> (Real,Real) -> 
--approx = h' (x,t)

-- Number in interval
data Interval : (a : Nat) -> (b : Nat) -> Type where
     intA : Interval a (a + k)
     intS : Interval (S a) ((S a) + k) -> Interval a (a + (S k))

-- If a number is in the interval, so is its successor in the successive interval
-- Probably should have a different name - intervalShift maybe?         
intervalSucc : (n : Interval a b) -> Interval (S a) (S b)
intervalSucc intA = intA
intervalSucc (intS i) = intS (intervalSucc i)
             
total               
natToInterval : Nat -> (a : Nat) -> (b : Nat) -> Maybe (Interval a b)
natToInterval Z Z _ = Just intA
natToInterval (S n) (S a) (S b) with (natToInterval n a b)
              | Just i = Just (intervalSucc i)
              | Nothing = Nothing
natToInterval (S n) Z (S b) with (natToInterval n Z b)
              | Just i = Just (intS (intervalSucc i))
              | Nothing = Nothing
natToInterval _ _ Z = Nothing
natToInterval Z _ _ = Nothing

total
integerToInterval : Integer -> (a : Nat) -> (b : Nat) -> Maybe (Interval a b)
integerToInterval n a b = if n >= 0 then natToInterval (cast n) a b else Nothing

-- isJust as defined in Fin
fromInteger : (n : Integer) ->
            { default ItIsJust
              prf : (IsJust (integerToInterval n a b))} ->
              Interval a b
fromInteger {a} {b} n {prf} with (integerToInterval n a b)
            fromInteger {a} {b} n {prf = ItIsJust} | Just i = i

-- instance Eq (Interval a b) where
-- --    (==) intA intA ?= True
-- --    (==) (intS k) (intS k') = k == k'
--     (==) _ _ = False

intervalToNat : (n : Interval a b) -> Nat
intervalToNat {a} intA = a
intervalToNat (intS n) = S (intervalToNat n)

-- A pred fin function
total
predFin : Fin n -> Fin n
predFin fZ = fZ
predFin (fS f) = weaken f

-- A successor function, similar to the pred function of nats, where Succ of the
-- last number in the set is the number itself.
-- This is more complicated due to the structure of Fin running in the other way.
total
succFin : Fin n -> Fin n
succFin (fS f) = fS (succFin f)
succFin {n = S (S k)} fZ = fS fZ -- Note the implicit type needs to be given explicitely here on the LHS
succFin fZ = fZ

-- Boolean predicates of the above:
total
hasProperPredFin : Fin n -> Bool
hasProperPredFin fZ = False
hasProperPredFin (fS _) = True

total
hasProperSuccFin : Fin n -> Bool
hasProperSuccFin {n = S (S k)} fZ = True
hasProperSuccFin fZ = False
hasProperSuccFin (fS f) = hasProperSuccFin f

-- A view of whether an element of Fin is the last element in it.
data LastFin : Fin n -> Type where
--     isLast  : (k : Nat)   -> LastFin (last {n = k})
     isLast  : LastFin (last {n = k}) -- equivalent to the above constructor definition 
     notLast : (f : Fin n) -> LastFin (weaken f)

total
isLastFin : {n : Nat} -> (f : Fin n) -> LastFin f
isLastFin {n = S (S k)} fZ = notLast fZ
isLastFin {n = S Z} fZ     = isLast {k = Z}
isLastFin (fS f) with (isLastFin f)
     isLastFin (fS (last {n = n'})) | isLast {k = n'} = isLast
     isLastFin (fS (weaken f'))     | notLast f' = notLast (fS f')

-- A view of whether an element of Fin is the last element in it.
data InteriorFin : (n : Nat) -> (c : Nat) -> (f : Fin (S n)) -> Type where
     exterior : (k : Nat) -> (o : Nat) -> (o' : Nat) -> InteriorFin (k + o) (S o + o') (weakenN o (last {n = k}))
     interior : (k : Nat) -> (c : Nat) -> (f : Fin (S k)) -> InteriorFin (k + c) c (weakenN c f)

weakenNZeroNeutral : {n : Nat} -> (f : Fin (S n)) -> (weakenN Z f = f)
weakenNZeroNeutral {n = k} fZ = rewrite (plusZeroRightNeutral k) in refl
weakenNZeroNeutral {n = S k} (fS f) = let ih = weakenNZeroNeutral f in ?cantMakeThisWork

total
isInteriorFin : (n : Nat) -> (c : Nat) -> (f : Fin (S n)) -> InteriorFin n c f
isInteriorFin n c fZ with (cmp n c)
              isInteriorFin n2 (n2 + S c2) fZ | cmpLT c2 = --in the boundary
                            rewrite sym (plusSuccRightSucc n2 c2) in
                            exterior Z n2 c2
              isInteriorFin c2 c2 fZ          | cmpEQ    = --last interior element
                            interior Z c2 (fZ {k = Z})
              isInteriorFin (c2 + S n2) c2 fZ | cmpGT n2 = --interior elements
                            rewrite (plusCommutative c2 (S n2)) in
                            interior (S n2) c2 (fZ {k = S n2})
isInteriorFin (S n) c (fS f) with (isInteriorFin n c f)
              isInteriorFin (S (k + c)) c (fS (weakenN c f')) | interior k c f'
                            = interior (S k) c (fS f')
              isInteriorFin (S (k + o)) (S o + o') (fS _)     | exterior k o o'
                            = exterior (S k) o o'
isInteriorFin Z _ (fS fZ) impossible                            

total
isInteriorFin2 : (c : Nat) -> (f : Fin (S n)) -> InteriorFin n c f
isInteriorFin2 {n = n'} c fZ with (cmp n' c)
              isInteriorFin2 {n = n2} (n2 + S c2) fZ | cmpLT c2 = --in the boundary
                            rewrite sym (plusSuccRightSucc n2 c2) in
                            exterior Z n2 c2
              isInteriorFin2 {n = c2} c2 fZ          | cmpEQ    = --last interior element
                            interior Z c2 (fZ {k = Z})
              isInteriorFin2 {n = (c2 + S n2)} c2 fZ | cmpGT n2 = --interior elements
                            rewrite (plusCommutative c2 (S n2)) in
                            interior (S n2) c2 (fZ {k = S n2})
isInteriorFin2 {n = (S n')} c (fS f) with (isInteriorFin n' c f)
              isInteriorFin2 {n = (S (k + c))} c (fS (weakenN c f')) | interior k c f'
                            = interior (S k) c (fS f')
              isInteriorFin2 {n = (S (k + o))} (S o + o') (fS _)     | exterior k o o'
                            = exterior (S k) o o'
isInteriorFin2 {n = Z} _ (fS fZ) impossible                            
 
   
isLastFin2 : Fin n -> Bool
isLastFin2 f = not (hasProperSuccFin f)

-- Poor man's version, doesn't use dependent types for righthand boundary,
-- thus indexes are not well typed-checked and we would have a hard time convincing
-- the compiler of totality of the function
approx : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT : Nat) -> (eX : Nat)
       -> (t : Fin eT) -> (x : Fin eX) -> Float
approx alpha dT dX eT2 eX2 =
       let r = alpha * dT / (dX * dX)
           in approx_inner where
              approx_inner : (t : Fin eT) -> (x : Fin eX) -> Float
              approx_inner _    fZ = 1.0
              approx_inner fZ   _  = 0.0
              approx_inner t x =
                           if isLastFin2 x
                              then 0.0 -- cold end
                              else approx_inner (predFin t) x
                                   +  c * (approx_inner (predFin t) (predFin x)
                                           - 2 * (approx_inner (predFin t) x)
                                           + approx_inner (predFin t) (succFin x))
                           where
                                c : Float
                                c = alpha * dT / (dX * 2)

-- Use with instead of if. A step towards solution. Had to explicitely pass in arguments, as I had problems with binding things properly otherwise.
approx2 : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT : Nat) -> (eX : Nat)
       -> (t : Fin eT) -> (x : Fin eX) -> Float
approx2 alpha dT dX eT2 eX2 =
       let r = alpha * dT / (dX * dX)
           in approx_inner eT2 eX2 where
              approx_inner : (eT : Nat) -> (eX : Nat) -> (t : Fin eT) -> (x : Fin eX) -> Float
              approx_inner _ _ _    fZ = 1.0
              approx_inner _ _ fZ   _  = 0.0
              approx_inner (S eT) (S eX) t x with (isLastFin {n = S eX} x)
                           approx_inner (S eT) (S eX) t (last {n = eX}) | isLast {k = eX} = 0.0
                           approx_inner (S eT) (S eX) t (weaken y)      | notLast y = approx_inner (S eT) (S eX) (predFin t) (weaken y)
                                                                                      +  c * (approx_inner (S eT) (S eX) (predFin t) (predFin (weaken y))
                                                                                      - 2 * (approx_inner (S eT) (S eX) (predFin t) (weaken y))
                                                                                      + approx_inner (S eT) (S eX) (predFin t) (fS y)) -- This is a win
                                                                                      where
                                                                                                c : Float
                                                                                                c = alpha * dT / (dX * 2)

-- This is not the way to make the binding work:
approx3 : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT2 : Nat) -> (eX2 : Nat)
       -> (t : Fin eT2) -> (x : Fin eX2) -> Float
approx3 alpha dT dX (S eT) (S eX) =
       let r = alpha * dT / (dX * dX) in
       approx_inner where
                    -- Hopefully the eT and eX are bound to the scope above, but I am not certain
                    approx_inner : (t : Fin eT2) -> (x : Fin eX2) -> Float 
                    approx_inner {eT2 = S eT} {eX2 = S eX} _   fZ = 1.0
                    approx_inner fZ   _  = 0.0
                    approx_inner {eX2 = S eX} t x with (isLastFin {n = S eX} x)
                           -- This shows how the implicit binding breaks.
                           approx_inner t (last {n = eX'}) | isLast {k = eX'} = approx_inner (predFin t) (fS (fS (last {n = eX'}))) 
                           approx_inner t (weaken y)       | notLast y = approx_inner (predFin t) (weaken y)
                                                                                      +  c * (approx_inner (predFin t) (predFin (weaken y))
                                                                                      - 2 * (approx_inner (predFin t) (weaken y))
                                                                                      + approx_inner (predFin t) (fS y))
                                                                                      where
                                                                                                c : Float
                                                                                                c = alpha * dT / (dX * 2)
-- Induction on time, have to fix induction on space
approx4 : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT : Nat) -> (eX : Nat)
       -> (t : Fin eT) -> (x : Fin eX) -> Float
approx4 alpha dT dX eT eX = approx_inner eT eX where
        approx_inner : (eT : Nat) -> (eX : Nat) -> (t : Fin eT) -> (x : Fin eX) -> Float
        approx_inner _ _ _    fZ = 1.0
        approx_inner _ _ fZ   _  = 0.0
        approx_inner (S (S eT)) (S (S eX)) (fS t) x with (isLastFin {n = S (S eX)} x)
                     approx_inner (S (S eT)) (S (S eX)) (fS t) (last {n = S eX}) | isLast {k = S eX} = 0.0
                     approx_inner (S (S eT)) (S (S eX)) (fS t) (weaken y)      | notLast y =
                                  let c = alpha * dT / (dX * dX) in
                                  let approx_inner' = approx_inner (S (S eT)) (S (S eX)) (weaken t) in
                                  approx_inner' (weaken y)
                                  +  c * (approx_inner' (predFin (weaken y))
                                         - 2.0 * approx_inner' (weaken y)
                                         + approx_inner' (fS y))

-- Both induction on time and space should be fine now.
-- No longer using the "unsafe" pred and succ functions.
-- We are able to get all the evidence needed for recursing on the correct elements.
-- We are still not able to prove the function total.
-- We can assert that (weaken t) is always smaller than (fS t), however that still does not work.
-- I think the recursive call on x confuses Idris into thinking that it might not actually be total.
-- However, as long as one argument is decreasing and reaching bottom on it is a terminal condition,
-- it shouldn't be a problem that the other argument increases. (It also can't increase in an unbounded
-- fashion, however proving that might be too difficult and I think is unnecessary.)
approx5 : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT : Nat) -> (eX : Nat)
       -> (t : Fin eT) -> (x : Fin eX) -> Float
approx5 alpha dT dX eT eX = approx_inner eT eX where
        approx_inner : (eT : Nat) -> (eX : Nat) -> (t : Fin eT) -> (x : Fin eX) -> Float
        approx_inner _ _ _    fZ = 1.0
        approx_inner _ _ fZ   _  = 0.0
        approx_inner (S (S eT)) (S (S eX)) (fS t) (fS x) with (isLastFin {n = S eX} x)
                     approx_inner (S (S eT)) (S (S eX)) (fS t) (fS (last {n = eX})) | isLast {k = eX} = 0.0
                     approx_inner (S (S eT)) (S (S eX)) (fS t) (fS (weaken y))      | notLast y =
                                  let c = alpha * (dT / (dX * dX)) in
                                  let ap = approx_inner (S (S eT)) (S (S eX)) (weaken t) in
                                  ap (fS (weaken y))
                                  +  c * (ap (weaken (weaken y))
                                          - 2.0 * ap (fS (weaken y))
                                          + ap (fS (fS y)))
        -- These two cases have to be stated to be explicitely impossible, idris can't figure that out by itself
        approx_inner (S Z) _     (fS fZ) _       impossible
        approx_inner _     (S Z) _       (fS fZ) impossible
-- the above could probably be generated from the discretization syntax

-- TODO figure out a minimal example of this failing.
approx_inner : (eT : Nat) -> (eX : Nat) -> (t : Fin eT) -> (x : Fin eX) -> Float
approx_inner _ _ _    fZ = 1.0
approx_inner _ _ fZ   _  = 0.0
approx_inner (S (S eT)) (S (S eX)) (fS t) (fS x) with (isLastFin {n = S eX} x)
                     approx_inner (S (S eT)) (S (S eX)) (fS t) (fS (last {n = eX})) | isLast {k = eX} = 0.0
                     approx_inner (S (S eT)) (S (S eX)) (fS t) (fS (weaken y))      | notLast y =
                                  let c = 1.0 in 
                                  let ap = approx_inner (S (S eT)) (S (S eX)) (assert_smaller (fS t) (weaken t)) in
                                  ap (fS (weaken y))
                                  +  c * (ap (fS (fS y))
                                          - 2.0 * ap (fS (weaken y))
                                          + ap (weaken (weaken y)))
approx_inner (S Z) _     (fS fZ) _       impossible
approx_inner _     (S Z) _       (fS fZ) impossible

-- Next steps:
-- Write a simple DSL to hide the verbosity.
-- Preservation of energy: can this be done algebraically/syntactically?
-- Matching model to implementation: verification of approximation - innitial ideas? Probably need to know more about approximation methods.
-- Write an effective (probably effectfull) version while hiding the effects.
--    Arrays in idris? If there are no arrays, could write a functional array with using bindings to C.
--    There is an effectful module Memory that allows us to allocate/work with external memory,
--    however all we really want/need is an immutable array with an allocator function, as that is inherently safer for our purposes.
--    (modulo reusing memory as in a double buffer - we probably can't prove to the compiler that we have no other references, so would
--     either have to do it manually/hide the double buffering behind an interface, while doing it manually inside, hopefully while using
--     effects to prove type safety.)
-- Implement other ideas such as units/dimension checking. Probably low priority as that has been done before?

-- Using the more general isInteriorFin instead of isLast view.
approx6 : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT : Nat) -> (eX : Nat)
       -> (t : Fin (S eT)) -> (x : Fin (S eX)) -> Float
approx6 alpha dT dX eT eX = approx_inner eT eX where
        approx_inner : (eT : Nat) -> (eX : Nat) -> (t : Fin (S eT)) -> (x : Fin (S eX)) -> Float
        approx_inner _ _ _    fZ = 1.0
        approx_inner _ _ fZ   _  = 0.0
        approx_inner (S eT) (S eX) (fS t) (fS x) with (isInteriorFin eX 1 x)
                     approx_inner (S eT) (S (eX' + Z)) (fS t) (fS _)
                                  | exterior eX' Z Z = 0.0
                     approx_inner (S eT) (S (eX' + (S Z))) (fS t) (fS (weakenN (S Z) y))
                                  | interior eX' (S Z) y =
                                  let c = alpha * (dT / (dX * dX)) in
                                  let ap = approx_inner (S eT) (S (S eX')) (weaken t) in
                                  ap (fS (weaken y))
                                  +  c * (ap (weaken (weaken y))
                                          - 2.0 * ap (fS (weaken y))
                                          + ap (fS (fS y)))
        approx_inner Z _ (fS fZ) _ impossible                                                        
        approx_inner _ Z _ (fS fZ) impossible
                                          

-- Not total as the compiler doesn't know that exterior eX' _ (S _) is impossible
approx_inner2 : (eT : Nat) -> (eX : Nat) -> (t : Fin (S eT)) -> (x : Fin (S eX)) -> Float
approx_inner2 _ _ _    fZ = 1.0
approx_inner2 _ _ fZ   _  = 0.0
approx_inner2 (S eT) (S eX) (fS t) (fS x) with (isInteriorFin eX 1 x)
             approx_inner2 (S eT) (S (eX' + Z)) (fS t) (fS _)
             | exterior eX' Z Z = 0.0
             approx_inner2 (S eT) (S (eX' + _)) (fS t) (fS _)
             | exterior eX' (S _) _ impossible 
             -- approx_inner2 (S eT) (S (eX' + Z)) (fS t) (fS _)
             -- | exterior eX' Z (S _) = 2.0
             -- The case above is said to be valid and when used, it marks the first case,
             -- i.e. exterior eX' Z Z as unreachable.
             approx_inner2 (S eT) (S (eX' + (S Z))) (fS t) (fS (weakenN (S Z) y))
             | interior eX' (S Z) y =
             let c = 1.0 in
             let ap = approx_inner2 (S eT) (S (S eX')) (weaken t) in
             ap (fS (weaken y))
                +  c * (ap (weaken (weaken y))
                       - 2.0 * ap (fS (weaken y))
                       + ap (fS (fS y)))
approx_inner2 Z _ (fS fZ) _ impossible
approx_inner2 _ Z _ (fS fZ) impossible

-- Problem: with the range being parametrized, it is hard to convince the compiler of the
-- impossibility of certain cases, as witnessed above.

--- Demonstrate how isInteriorFin can be used when relating to successor and its successor
--- via a reversed fibonacci sequence
fib : (n : Nat) -> Fin (S n) -> Nat
fib n x with (isInteriorFin n 2 x)
     fib (n' + Z) _               | exterior n' Z (S Z) = 0
     fib (n' + (S Z)) _           | exterior n' (S Z) Z = 1
     fib _ (weakenN (S (S Z)) x') | interior n' (S (S Z)) x'
         = fib (S (S n')) (weaken (fS x'))
         + fib (S (S n')) (fS (fS x'))

succPlusZeroRightNeutral : (k : Nat) -> (S (plus k Z) = S k)
succPlusZeroRightNeutral k = rewrite (plusZeroRightNeutral k) in refl

finSuccPlusZeroRightNeutral : (k : Nat) -> (Fin (S (plus k Z)) = Fin (S k))
finSuccPlusZeroRightNeutral k = rewrite (plusZeroRightNeutral k) in refl

createRev : (n : Nat) -> (f : (Nat -> a)) -> Vect n a
createRev Z _ = []
createRev (S n) f = f n::createRev n f

create : (n : Nat) -> (f : (Nat -> a)) -> Vect n a
create n f = reverse (createRev n f)

lastIsLast : (k : Nat) -> (finToNat (last {n = k}) = k)
lastIsLast Z = refl
lastIsLast (S k') = rewrite (lastIsLast k') in refl

weakenPreservesValue : (f : Fin n) -> (finToNat (weaken f) = finToNat f)
weakenPreservesValue fZ = refl
weakenPreservesValue (fS f) = rewrite (weakenPreservesValue f) in refl

create_ : (f : Fin (S n) -> a) -> (k : Fin (S n)) -> Vect (S (finToNat k)) a
create_ f fZ = [f fZ]
create_ {n = S _} f (fS k) = rewrite sym (weakenPreservesValue k) in f (fS k)::create_ f (weaken k)

createFin : (f : Fin (S n) -> a) -> Vect (S n) a
createFin {n = k} f = rewrite sym (lastIsLast k) in reverse (create_ f (last {n = k}))

createFinCorrect : (f : Fin (S n) -> a) -> (k : Fin (S n)) -> (index k (createFin f) = f k)
createFinCorrect f fZ = ?asdf

memoize : {a : Type} -> (n : Nat) -> (Fin (S n) -> a) -> Fin (S n) -> a
memoize {a = a} n f = let mem : Vect (S n) (Lazy a) = createFin (\x : Fin (S n) => (f x)) in (\x => index x mem)

memoizeCorrect : (f : (Fin (S n) -> a)) -> (k : Fin (S n)) -> (memoize n f k = f k)
memoizeCorrect f k = ?asd

-- A version failing to use memoization. This might prove more difficult than expected.
approx7 : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT : Nat) -> (eX : Nat)
-> (t : Fin (S eT)) -> (x : Fin (S eX)) -> Float
approx7 alpha dT dX eT' eX' = approx_inner {eT = eT'} {eX = eX'} where
        mutual
                approx_inner : {eT : Nat} -> {eX : Nat} -> (t : Fin (S eT)) -> (x : Fin (S eX)) -> Float
                approx_inner _    fZ = 1.0
                approx_inner fZ   _  = 0.0
                approx_inner {eT = S eTa} {eX = S eXa} (fS t) (fS x) with (isInteriorFin eXa 1 x)
                     approx_inner {eT = S eTb} {eX = S (eXb + Z)} (fS t) (fS _)
                                  | exterior eXb Z Z = 0.0
                     approx_inner {eT = (S eTb)} {eX = (S (eXb + (S Z)))} (fS t) (fS (weakenN (S Z) y))
                                  | interior eXb (S Z) y =
                                  let c = alpha * (dT / (dX * dX)) in
                                  let ap = approx_mem'd {eT = (S eTb)} {eX = (S (S eXb))} (weaken t) in
                                  ap (fS (weaken y))
                                  +  c * (ap (weaken (weaken y))
                                          - 2.0 * ap (fS (weaken y))
                                          + ap (fS (fS y)))
                approx_inner {eT = Z} (fS fZ) _ impossible
                approx_inner {eX = Z} _ (fS fZ) impossible

                approx_mem'd : {eT : Nat} -> {eX : Nat} -> (t : Fin (S eT)) -> (x : Fin (S eX)) -> Float
                approx_mem'd {eT = eTa} {eX = eXa} =
                             memoize eTa (\t : Fin (S eTa) =>
                                     memoize eXa (\x : Fin (S eXa) => approx_inner {eT = eTa} {eX = eXa} t x))

-- Returns the complement number in the given set

total
complement : (Fin n) -> (Fin n)
complement {n = (S _)}     fZ     = last
complement {n = (S (S _))} (fS i) = weaken (complement i)
complement {n = (S Z)} (fS fZ) impossible

reverseCorrect : (v : Vect n a) -> (i : Fin n) -> (index i v = index (complement i) (reverse v))
reverseCorrect {n = S Z} v fZ = ?rC_base

--reverseCorrect {n = Z} _ fZ impossible

-- Indexes from 0 to (n-1)
indexes : {n : Nat} -> Vect n (Fin n)
indexes {n = Z} = []
indexes {n = S n'} = fZ::map fS indexes

-- We try to compute a function iteratively, folding over the toplevel dimension (time) and the lower level
-- dimension. (Mapping on x is not appropriate as we want to index into different parts of the list.)

foldX : {m : Nat} -> Vect m a -> (f : (Vect m a ->  Fin m -> a)) -> Vect m a
foldX a f = map (f a) indexes

-- Perhaps hide the implementation? This essentially makes this a memoize function.
foldXf : {m : Nat} -> (Fin m -> a) -> ((Fin m -> a) -> Fin m -> a) -> Fin m -> a
foldXf f f2 = let a = map (f2 f) indexes in -- Need this part to be evaluated just once.
                                            -- TODO find order of evaluation
              (\x => index x a)

-- Probably a better definition of memoize                            
memoize' : {n : Nat} -> (Fin n -> a) -> Fin n -> a
memoize' f = let a = map f indexes in
         \i => index i a

-- In this particular case, we just want to iterate over T.  
foldTX : {m : Nat} -> (n : Nat) -> (acc : Vect m a) -> (f : (Vect m a -> Fin m -> a)) -> Vect m a
foldTX Z     acc _ = acc
foldTX (S n) acc f = foldTX n (foldX acc f) f

foldTXf : {m : Nat} -> (n : Nat) -> (init : Fin m -> a) -> (step : (Fin m -> a) -> Fin m -> a) -> Fin m -> a
foldTXf Z     init _ = init
foldTXf (S n) init f = foldTXf n (foldXf init f) f

-- exponentiate function with memoization
expF : {a : Type} -> Nat -> (Fin n -> a) -> ((Fin n -> a) -> Fin n -> a) -> Fin n -> a
expF Z     init _ = init
expF (S n) init f = expF n (memoize' (f init)) f

-- An alternative definition using fold over vectors. Maybe not the nicest implementation?
expF' : {a : Type} -> Nat -> (Fin n -> a) -> ((Fin n -> a) -> Fin n -> a) -> Fin n -> a
expF' n init f = foldr (\f => \acc => memoize' (f acc)) init (Vect.replicate n f)

weaken' : Fin n -> Fin (n + 1)
weaken' fZ = fZ
weaken' (fS k) = believe_me (fS (weaken k))

fS' : {n : Nat} -> Fin n -> Fin (n + 1)
fS' {n = n'} f = believe_me (fS f)

-- Bonus: we get a nice decoupling this way, as the state only strictly depends on the previous state, not necessarily
-- on the actual timestep. (Had that in previous definitions as well, but is an important notion. Perhaps we could
-- enforce this even further, decouple plumbing and data.)
approx8 : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT : Nat) -> (eX : Nat) -> (t : Fin (S eT)) -> (x : Fin (S eX)) -> Float
approx8 alpha dT dX eT' eX' = (\t => \x => index x (foldTX (finToNat t) (map initial indexes) step)) where
        initial : Fin eX -> Float
        initial fZ = 1.0
        initial _  = 0.0

        step : Vect (S eX) Float -> Fin (S eX) -> Float
        step _ fZ = 1.0
        step {eX = S eX'} a (fS x) with (isInteriorFin eX' 1 x)
             step {eX = S (eXb + Z)} a (fS _)
             | exterior eXb Z Z = 0.0
             step {eX = (S (eXb + (S Z)))} a (fS (weakenN (S Z) y))
             | interior eXb (S Z) y =
               let c = alpha * (dT / (dX * dX)) in
               let app  =  (\i => index i a) in
                 app (fS (weaken' y))
                    +  c * (app (weaken (weaken' y))
                               - 2.0 * app (fS (weaken' y))
                               + app (fS (fS' y)))
        step {eX = Z} _ (fS fZ) impossible


-- Bonus: we get a nice decoupling this way, as the state only strictly depends on the previous state, not necessarily
-- on the actual timestep. (Had that in previous definitions as well, but is an important notion. Perhaps we could
-- enforce this even further, decouple plumbing and data.)
approx9 : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT : Nat) -> (eX : Nat) -> (t : Fin (S eT)) -> (x : Fin (S eX)) -> Float
approx9 alpha dT dX eT' eX' = (\t => foldTXf (finToNat t) initial step) where
        initial : Fin (S n) -> Float
        initial fZ = 1.0
        initial _  = 0.0

        step : (Fin (S eX) -> Float) -> Fin (S eX) -> Float
        step _ fZ = 1.0
        step {eX = S eX'} prevT (fS x) with (isInteriorFin eX' 1 x)
             step {eX = S (eXb + Z)} prevT (fS _)
             | exterior eXb Z Z = 0.0
             step {eX = (S (eXb + (S Z)))} prevT (fS (weakenN (S Z) y))
             | interior eXb (S Z) y =
               let c = alpha * (dT / (dX * dX)) in
                 prevT (fS (weaken' y))
                    +  c * (prevT (weaken (weaken' y))
                               - 2.0 * prevT (fS (weaken' y))
                               + prevT (fS (fS' y)))
        step {eX = Z} _ (fS fZ) impossible


approx10 : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT : Nat) -> (eX : Nat) -> (t : Fin (S eT)) -> (x : Fin (S eX)) -> Float
approx10 alpha dT dX eT' eX' t = expF (finToNat t) initial step where
        initial : Fin (S n) -> Float
        initial fZ = 1.0
        initial _  = 0.0

        step : (Fin (S eX) -> Float) -> Fin (S eX) -> Float
        step _ fZ = 1.0
        step {eX = S eX'} prevT (fS x) with (isInteriorFin eX' 1 x)
             step {eX = S (eXb + Z)} prevT (fS _)
             | exterior eXb Z Z = 0.0
             step {eX = (S (eXb + (S Z)))} prevT (fS (weakenN (S Z) y))
             | interior eXb (S Z) y =
               let c = alpha * (dT / (dX * dX)) in
                 prevT (fS (weaken' y))
                    +  c * (prevT (weaken (weaken' y))
                               - 2.0 * prevT (fS (weaken' y))
                               + prevT (fS (fS' y)))
        step {eX = Z} _ (fS fZ) impossible
