-- Module providing relative indexing. Currently only indexes of middle, first, last.
module Relative

-- Always have 0 and 1 indexes, making first and last always different.
-- Maybe aliasing is not enough as values are always exposed?
-- We probably need to have an actual constructor.

abstract
data Index : Nat -> Type where
     In : (i : Fin (S (S n))) -> Index n
--Index : Nat -> Type
--Index n = Fin (S (S n))

-- abstract
-- lift : Fin (S (S n)) -> Index n
-- lift i = i

abstract
lift : Fin (S (S n)) -> Index n
lift i = In i

-- Position evidence.
-- A total partitionining ensured by the types.
-- If there is only one element, it is said to be first, not last.
-- abstract data first_el : (n : Nat) -> Index n -> Type where
--      First_el : first_el n (fZ {k = S n})

-- abstract data center_el : (n : Nat) -> Index n -> Type where
--      Center_el : (f : Fin  n) -> center_el n (weaken (fS f))

-- abstract data last_el   : (n : Nat) -> Index n -> Type where
--      Last_el : last_el k (last {n = S k})

--bottom/interior/top
abstract data first_el : (n : Nat) -> Index n -> Type where
     First_el : first_el n (In (fZ {k = S n}))

abstract data center_el : (n : Nat) -> Index n -> Type where
     Center_el : (f : Fin  n) -> center_el n (In (weaken (fS f)))

abstract data last_el   : (n : Nat) -> Index n -> Type where
     Last_el : last_el k (In (last {n = S k}))

-- A view of the position
public
data position : Index n     -> Type where
     First  : first_el  n i -> position i
     Center : center_el n i -> position i
     Last   : last_el   n i -> position i

-- Compute the view:
-- Apparently not total?

abstract
compute_position : (i : Index n) -> position i
compute_position (In fZ)      = First First_el
compute_position {n = Z} (In (fS fZ)) = Last Last_el
compute_position {n = S n'} (In (fS i)) with (compute_position (In i))
                 compute_position (In (fS fZ)) | First First_el = Center (Center_el fZ)
                 compute_position (In (fS (weaken (fS f)))) | Center (Center_el f) = Center (Center_el (fS f))
                 compute_position {n = S n''} (In (fS (last {n = S n''}))) | Last (Last_el {k = n''}) = Last Last_el
compute_position {n = Z} (In (fS (fS fZ))) impossible

-- Couldn't quite get this to work without pulling out the explicit n parameter, i.e.

-- class HasPrev (pos : Index n -> Type) where
--       prev : {i : Index n} -> (prf : pos i) -> Vect n a -> a

-- does not work, probably due to the type class not allowing implicit arguments.
-- We therefore had to make the arguments for the type constructors of positions explicit
-- as well.
                  
-- class HasPrev (pos : (n : Nat) -> Index n -> Type) where
--       -- Cannot make the proof implicit.
--       prev : {n : Nat} -> {i : Index n} -> (prf : pos n i) -> Vect (S (S n)) a -> a
      
---- Explicit prev and next functions. Maybe not what we want?      
-- instance HasPrev center_el where
--          prev (Center_el f) v = Vect.index (weaken (weaken f)) v
         
-- instance HasPrev last_el where
--          prev Last_el v = Vect.index (weaken last) v
         
-- class HasNext (pos : (n : Nat) -> Index n -> Type) where
--       next : {n : Nat} -> {i : Index n} -> (prf : pos n i) -> Vect (S (S n)) a -> a
         
-- instance HasNext first_el where
--          next First_el v = Vect.index (fS fZ) v
        
-- instance HasNext center_el where
--          next (Center_el f) v = Vect.index (fS (fS f)) v

public
indexToNat : Index n -> Nat
indexToNat (In i) = finToNat i

public                                                      
class HasNext (pos : (n : Nat) -> Index n -> Type) where
      total public
      iS : (prf : pos n i) -> Index n
-- Can't do the following for some reason?
      -- total public
      -- iS_correct : (prf : pos n i) -> (indexToNat i + 1 = indexToNat (iS prf)) --iS prf)   --((indexToNat (iS {n = n'} {i = i'} prf)) = 1)
      
instance HasNext first_el where
         iS First_el = In (fS fZ)
      
instance HasNext center_el where
         iS (Center_el f) = In (fS (fS f))

public
class HasPrev (pos : (n : Nat) -> Index n -> Type) where
      iP : {n : Nat} -> {i : Index n} -> (prf : pos n i) -> Index n
-- Again, the following doesn't work      
--      iP_correct : (prf : pos n i) -> (indexToNat i = indexToNat (iP prf ) + 1)

instance HasPrev center_el where
         iP (Center_el f) = In (weaken (weaken f))
      
instance HasPrev last_el where
         iP Last_el = In (weaken last)

abstract
index : {n : Nat} -> (i : Index n) -> Vect (S (S n)) a -> a
index (In i) v = index i v


instance Eq (Index n) where
    (==) (In i1) (In i2) = i1 == i2

public
class HasNeutral (pos : (n : Nat) -> Index n -> Type) where {
      iN : {n : Nat} -> {i : Index n} -> (prf : pos n i) -> Index n
--      iN_correct : {n : Nat} -> (prf : pos n i) -> (iN prf = i)
}      
      
instance HasNeutral first_el where
         iN First_el = In (fZ)

instance HasNeutral center_el where
         iN (Center_el f) = In (weaken (fS f))

instance HasNeutral last_el where
         iN Last_el = In (fS last)
