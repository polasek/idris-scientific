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
data InteriorFin : (n : Nat) -> (c : Nat) -> (f : Fin n) -> Type where
     exterior : (k : Nat) -> (o : Nat) -> (o' : Nat) -> InteriorFin (S k + o) (S o + o') (weakenN o (last {n = k}))
     interior : (k : Nat) -> (c : Nat) -> (f : Fin k) -> InteriorFin (plus k c) c (weakenN c f)

weakenNZeroNeutral : {n : Nat} -> (f : Fin (S n)) -> (weakenN Z f = f)
weakenNZeroNeutral {n = k} fZ = rewrite (plusZeroRightNeutral k) in refl
weakenNZeroNeutral {n = S k} (fS f) with (weakenNZeroNeutral f)
                   weakenNZeroNeutral {n = S k} (fS f) | eq = ?cantMakeThisWork
                    -- cong eq --  ?asd --cong eq {f = fS} --rewrite sym (plusZeroRightNeutral k) in

--Totality checker broken?
isInteriorFin : (n : Nat) -> (c : Nat) -> (f : Fin n) -> InteriorFin n c f
isInteriorFin (S n) c fZ with (cmp n c)
              isInteriorFin (S n2) (n2 + S c2) fZ | cmpLT c2 = --in the boundary
                            rewrite sym (plusSuccRightSucc n2 c2) in
                            exterior Z n2 c2
              isInteriorFin (S c2) c2 fZ          | cmpEQ    = --last interior element
                            interior (S Z) c2 (fZ {k = Z})
              isInteriorFin (S (c2 + S n2)) c2 fZ | cmpGT n2 = --interior elements
                            rewrite (plusCommutative c2 (S n2)) in
                            interior (S (S n2)) c2 (fZ {k = S n2})
isInteriorFin (S n) c (fS f) with (isInteriorFin n c f)
              isInteriorFin (S (plus k c)) c (fS (weakenN c f')) | interior k c f'
                            = interior (S k) c (fS f')
              isInteriorFin (S (S k + o)) (S o + o') (fS _)      | exterior k o o'
                            = exterior (S k) o o'

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


-- -- A view of whether an element of Fin is the last element in it.
-- data InteriorFin : (n : Nat) -> (c : Nat) -> (f : Fin n) -> Type where
--      exterior : (k : Nat) -> (o : Nat) -> (o' : Nat) -> InteriorFin (S k + o) (S o + o') (weakenN o (last {n = k}))
--      interior : (k : Nat) -> (c : Nat) -> (f : Fin k) -> InteriorFin (plus k c) c (weakenN c f)


-- approx6 : (alpha : Float) -> (dT : Float) -> (dX : Float) -> (eT : Nat) -> (eX : Nat)
--        -> (t : Fin eT) -> (x : Fin eX) -> Float
-- approx6 alpha dT dX eT eX = approx_inner eT eX where
--         approx_inner : (eT : Nat) -> (eX : Nat) -> (t : Fin eT) -> (x : Fin eX) -> Float
--         approx_inner _ _ _    fZ = 1.0
--         approx_inner _ _ fZ   _  = 0.0
--         approx_inner (S (S eT)) (S (S eX)) (fS t) (fS x) with (isInteriorFin (S eX) 1 x)
--                      approx_inner (S (S eT)) (S (S eX)) (fS t) (fS _) | exterior eX Z Z = 0.0
--                      -- approx_inner (S (S eT)) (S (S eX)) (fS t) (fS (weaken y))      | notLast y =
--                      --              let c = alpha * (dT / (dX * dX)) in
--                      --              let ap = approx_inner (S (S eT)) (S (S eX)) (weaken t) in
--                      --              ap (fS (weaken y))
--                      --              +  c * (ap (weaken (weaken y))
--                      --                      - 2.0 * ap (fS (weaken y))
--                      --                      + ap (fS (fS y)))
--         -- These two cases have to be stated to be explicitely impossible, idris can't figure that out by itself
--         approx_inner (S Z) _     (fS fZ) _       impossible
--         approx_inner _     (S Z) _       (fS fZ) impossible


