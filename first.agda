data Zero : Set where
  -- No constructor, as this is impossible

record One : Set where
  constructor <>
  -- Trivial constructor

-- Sum type
data _+_ (S T : Set) : Set  where
  inl : S -> S + T
  inr : T -> S + T

-- Product type
record _*_ (S T : Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T

-- Let's start proving things.
-- Transform evidence for the hypothesis into
-- evidence for the conclusion
-- Commutativity!

-- Starting point
-- comm : {A B : Set} -> A * B -> B * A
-- comm x = ?
-- C^c C^l -> load
-- C^c C^, -> show goal type and context
-- C^c C^c (on the variable within the goal) -> unpacks
-- C^c C^r -> introdcution forms
-- C^c C^a -> I'm feeling lucky
comm : {A B : Set} -> A * B -> B * A
comm (fst , snd) = snd , fst

-- Associativity
-- assoc : {A B C : Set} -> (A + B) + C -> A + (B + C)
-- assoc x = ?
assoc : {A B C : Set} -> (A + B) + C -> A + (B + C)
assoc (inl (inl a)) = inl a
assoc (inl (inr b)) = inr (inl b)
assoc (inr c) = inr (inr c)

-- Impossibility! False -> Something
imposs : { X : Set } -> Zero -> X
imposs ()

-- Messing with products.
-- If there's a function that transforms A to A'
-- and a function that transforms B to B'
-- I can build a function that transforms the pair <A, A'>
-- into the pair <B, B'>
-- Alternatively, if I know that A implies A' and B implies B'
-- then I can show that A AND B implies A' AND B'
-- _$*_ : {A B A' B' : Set} -> (A -> A') -> (B -> B') -> A * B -> A' * B'
-- (f $* g) x = ?
_$*_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A * B -> A' * B'
(f $* g) (fst , snd) = f fst , g snd

-- Similarly, messing with sums.
-- _$+_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A + B -> A' + B'
-- (f $+ g) x = ?
_$+_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A + B -> A' + B'
(f $+ g) (inl a) = inl (f a)
(f $+ g) (inr b) = inr (g b)
