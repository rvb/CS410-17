{-# OPTIONS --type-in-type #-}  -- yes, I will let you cheat in this exercise
{-# OPTIONS --allow-unsolved-metas #-}  -- allows import, unfinished

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CS410 2017/18 Exercise 3  WINDOWS AND OTHER STORIES (worth 25%)
------------------------------------------------------------------------------
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Dependencies
------------------------------------------------------------------------------

open import CS410-Prelude
open import CS410-Categories
open import Ex2


------------------------------------------------------------------------------
--  PART I:  Splittings
------------------------------------------------------------------------------

-- The type    ls <[ ms ]> rs
-- is similar to that found in Lec2.agda, but it works on lists, not numbers.
-- It provides the evidence that a list ms can be split into a left sublist ls
-- and a right sublist rs. In effect, it's a vector of bits that say which
-- elements of ms go left and which go right.

data _<[_]>_ {X : Set} : List X -> List X -> List X -> Set where
  sz : [] <[ [] ]> []
  sl : forall {l ls ms rs} -> ls <[ ms ]> rs -> (l ,- ls) <[ l ,- ms ]> rs
  sr : forall {r ls ms rs} -> ls <[ ms ]> rs -> ls <[ r ,- ms ]> (r ,- rs)


--??--3.1-(4)-----------------------------------------------------------------

-- Adapt _>[_]<_ from Lec2 to work for All. Given a P for each element of
-- ls and rs, riffle them together to get Ps for all the ms.

_>[_]<_ : {X : Set}{ls ms rs : List X} -> {P : X -> Set} ->
          All P ls -> ls <[ ms ]> rs -> All P rs ->
          All P ms
pl >[ sz ]< pr = <>
(pl , pls) >[ sl s ]< pr = pl , (pls >[ s ]< pr)
pl >[ sr s ]< (pr , prs) = pr , (pl >[ s ]< prs)

-- Now, buikd the view that shows riffling can be inverted, using a splitting
-- as the instructions to discover how to split an All in two.

data IsRiffle {X : Set}{ls ms rs : List X}(s : ls <[ ms ]> rs){P : X -> Set}
  : All P ms -> Set where
  mkRiffle : (pl : All P ls)(pr : All P rs) -> IsRiffle s (pl >[ s ]< pr)
  
isRiffle : {X : Set}{ls ms rs : List X}(s : ls <[ ms ]> rs)
           {P : X -> Set}(pm : All P ms) -> IsRiffle s pm
isRiffle sz <> = mkRiffle <> <>
isRiffle (sl s) (l , pm) with isRiffle s pm
isRiffle (sl s) (l , .(pl >[ s ]< pr)) | mkRiffle pl pr = mkRiffle (l , pl) pr
isRiffle (sr s) (r , pm) with isRiffle s pm
isRiffle (sr s) (r , .(pl >[ s ]< pr)) | mkRiffle pl pr = mkRiffle pl (r , pr)

--??--------------------------------------------------------------------------


--??--3.2-(4)-----------------------------------------------------------------

-- Construct the "all on the right" splitting.

srs : forall {X : Set}{xs : List X} -> [] <[ xs ]> xs
srs {xs = []} = sz
srs {xs = x ,- xs} = sr srs

-- Construct a view to show that any "none on the left" splitting is
-- "all on the right". Come up with the type yourself.


-- Construct the splitting that corresponds to concatenation.

slrs : forall {X : Set}(xs ys : List X) -> xs <[ xs +L ys ]> ys
slrs [] ys = srs
slrs (x ,- xs) ys = sl (slrs xs ys)

--??--------------------------------------------------------------------------

--??--3.3-(4)-----------------------------------------------------------------

-- Invent other useful operations which transform splittings.
-- You will need some to do later parts of the exercise, so maybe
-- wait until you see what you need.

-- I expect you will need at least something that takes a pair of splittings
-- that make a tree, like
--
--                  ms
--               <[    ]>
--            ls          rs
--                     <[    ]>
--                 lrs          rrs
--
-- and compute a "rotated" pair of splittings like
--
--                  ms
--               <[    ]>
--            ??          rrs
--         <[    ]>
--      ls          lrs

rotate : ∀ {X} {ls ms rs lrs rrs : List X} → ls <[ ms ]> rs → lrs <[ rs ]> rrs → Sg (List X) λ xs → (ls <[ xs ]> lrs) * (xs <[ ms ]> rrs)
rotate sz sz = [] , (sz , sz)
rotate (sl s1) s2 with rotate s1 s2
rotate (sl s1) s2 | xs , s1' , s2' = (_ ,- xs) , ((sl s1') , (sl s2'))
rotate (sr s1) (sl s2) with rotate s1 s2
rotate (sr s1) (sl s2) | xs , s1' , s2' = (_ ,- xs) , ((sr s1') , (sl s2'))
rotate (sr s1) (sr s2) with rotate s1 s2
rotate (sr s1) (sr s2) | xs , s1' , s2' = xs , (s1' , sr s2')

rotate' : ∀ {X} {ls ms rs lrs rrs : List X} → ls <[ ms ]> lrs → ms <[ rs ]> rrs → Sg (List X) λ xs → (ls <[ rs ]> xs) * (lrs <[ xs ]> rrs)
rotate' {rs = rs} sz s2 = rs , (srs , s2)
rotate' (sl s1) (sl s2) with rotate' s1 s2
rotate' (sl s1) (sl s2) | xs , s1' , s2' = _ , ((sl s1') , s2')
rotate' (sl s1) (sr s2) with rotate' (sl s1) s2
rotate' (sl s1) (sr s2) | xs , s1' , s2' = _ , ((sr s1') , (sr s2'))
rotate' (sr s1) (sl s2) with rotate' s1 s2
rotate' (sr s1) (sl s2) | xs , s1' , s2' = _ , ((sr s1') , (sl s2'))
rotate' (sr s1) (sr s2) with rotate' (sr s1) s2
rotate' (sr s1) (sr s2) | xs , s1' , s2' = _ , ((sr s1') , (sr s2'))

-- HINT: Sg is your friend

-- You'll probably need some other stuff, too.

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
--  PART II:  Permutations
------------------------------------------------------------------------------

-- When is one list a permutation of another?

data _~_ {X : Set} : List X -> List X -> Set where

  -- [] is a permutation of []
  []   : [] ~ []

  -- if xs ~ ys, then (x ,- xs) is a permutation of any list made by
  -- shoving x somewhere into ys
  _,-_ : forall {x xs ys' ys} ->
           (x ,- []) <[ ys' ]> ys ->
           xs ~ ys ->
           (x ,- xs) ~ ys'


--??--3.4-(1)-----------------------------------------------------------------

-- Show that every list is a permutation of itself.

reflP : {X : Set}{xs : List X} -> xs ~ xs
reflP {xs = []} = []
reflP {xs = x ,- xs} = (sl srs) ,- reflP

--??--------------------------------------------------------------------------


--??--3.5-(5)-----------------------------------------------------------------

--Splits can be mirrored, i.e. left and right parts swapped.
mirror : ∀ {X} {xs ys zs : List X} → xs <[ ys ]> zs → zs <[ ys ]> xs
mirror sz = sz
mirror (sl s) = sr (mirror s)
mirror (sr s) = sl (mirror s)

--Rippling together parts that are permutations of each other results in lists that are permutations of each other.
ripplePermutation : ∀ {X : Set} {xs ys zs xs' ys' zs' : List X} → xs <[ ys ]> zs → xs' <[ ys' ]> zs' → xs ~ xs' → zs ~ zs' → ys ~ ys'
ripplePermutation sz sz [] [] = []
ripplePermutation (sl s1) s2 (x ,- px) pz with rotate' x s2
ripplePermutation (sl s1) s2 (x ,- px) pz | qs , s2l , s2r = s2l ,- (ripplePermutation s1 s2r px pz)
ripplePermutation (sr s1) s2 px (x ,- pz) with rotate s2 x
ripplePermutation (sr s1) s2 px (x ,- pz) | xs , s2l , s2r with rotate' (mirror s2l) s2r
ripplePermutation (sr s1) s2 px (x ,- pz) | xs , s2l , s2r | ys , s2l' , s2r' = s2l' ,- ripplePermutation s1 s2r' px pz

-- Construct an "unbiased" insertion operator which lets you grow a
-- permutation by inserting a new element anywhere, left and right.

insP : forall {X : Set}{z : X}{xs xs' ys ys'} ->
         (z ,- []) <[ xs' ]> xs ->
         (z ,- []) <[ ys' ]> ys ->
         xs ~ ys -> xs' ~ ys'
insP l r p = ripplePermutation l r reflP p

-- Now show that, given a permutation, and any element on the left,
-- you can find out where it ended up on the right, and why the
-- remaining elements form a permutation.

findLonR : forall {X : Set}{z : X}{xs xs' ys'} ->
                  (z ,- []) <[ xs' ]> xs ->
                  xs' ~ ys' ->
                  Sg (List X) λ ys → xs ~ ys * (z ,- []) <[ ys' ]> ys
findLonR s p = {!!}

-- HINT: again, you may need Sg to give a sensible return type.

--??--------------------------------------------------------------------------


--??--3.6-(5)-----------------------------------------------------------------

-- Show that permutation is transitive.

transP : {X : Set}{xs ys zs : List X} -> xs ~ ys -> ys ~ zs -> xs ~ zs
transP p q = {!!}

-- HINT: you will need to define some useful operations on splittings to
-- get this to work.

-- HINT: this may help you figure out what you need for findLonR

-- For a small bonus, show that permutations are the morphisms of a
-- Category.

-- Show that permutation is symmetric.

symP : {X : Set}{xs ys : List X} -> xs ~ ys -> ys ~ xs
symP p = {!!}

-- A category where all morphisms are invertible is called a "groupoid".

--??--------------------------------------------------------------------------


--??--3.7-(2)-----------------------------------------------------------------

-- Make permutations act on All.

permute : {X : Set}{xs ys : List X} -> xs ~ ys ->
          {Q : X -> Set} -> All Q xs -> All Q ys

permute p qs = {!!}

--??--------------------------------------------------------------------------



-- MORE TO FOLLOW

-- AGAIN, "MORE" BECAME CLEARLY SURPLUS TO REQUIREMENTS
