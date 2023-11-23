||| Complex number.
|||
||| Copyright 2021, HATTORI, Hiroki
||| This file is released under the MIT license, see LICENSE for more detail.
|||
module Data.Complex

import Generics.Derive
import Derive.Eq
%language ElabReflection

-- --------------------------------------------------------------------------

public export
record Complex t where
  constructor MkComplex
  real : t
  imag : t


export
Show t => Show (Complex t) where
  showPrec d x = showParens (d >= PrefixMinus) "\{show x.imag}i + \{show x.real}"

export
Functor Complex where
  map f x = MkComplex (f x.real) (f x.imag)

%runElab derive "Complex" [Generic, Meta, Derive.Eq.Eq]

export
(Neg t, Num t) => Num (Complex t) where
  x + y = MkComplex (x.real + y.real) (x.imag + y.imag)
  x * y = MkComplex (x.real * y.real - x.imag * y.imag)
                    (x.real * y.imag + x.imag * y.real)
  fromInteger x = MkComplex (fromInteger x) (fromInteger 0)


export
Neg t => Neg (Complex t) where
  negate x = MkComplex (negate x.real) (negate x.imag)
  x - y    = MkComplex (x.real - y.real) (x.imag - y.imag)


export
isReal : (Num t, Eq t) => Complex t -> Bool
isReal x = x.imag == fromInteger 0


export
isImage : (Num t, Eq t) => Complex t -> Bool
isImage x = x.real == fromInteger 0



-- --------------------------------------------------------------------------

export
plus_commutative : (Num t, Neg t)
    => {comm_t: {a,b:t} -> (a + b) = (b + a)}
    -> {x, y:Complex t}
    -> (x + y) = (y + x)
plus_commutative = rewrite (comm_t {a=x.real} {b=y.real})
                in rewrite (comm_t {a=x.imag} {b=y.imag})
                in Refl

export
plus_associative : (Num t, Neg t)
    => {assoc_t: {a,b,c:t} -> (a + b) + c = a + (b + c)}
    -> {x, y, z:Complex t}
    -> (x + y) + z = x + (y + z)
plus_associative = rewrite (assoc_t {a=x.real} {b=y.real} {c=z.real})
                in rewrite (assoc_t {a=x.imag} {b=y.imag} {c=z.imag})
                in Refl

export
mult_commutative : (Num t, Neg t)
    => {mult_comm_t: {a,b:t} -> a * b = b * a}
    -> {plus_comm_t: {a,b:t} -> a + b = b + a}
    -> {x, y:Complex t}
    -> (x * y) = (y * x)
mult_commutative = rewrite (mult_comm_t {a=x.real} {b=y.real})
                in rewrite (mult_comm_t {a=x.imag} {b=y.imag})
                in rewrite (mult_comm_t {a=x.real} {b=y.imag})
                in rewrite (mult_comm_t {a=x.imag} {b=y.real})
                in rewrite (plus_comm_t {a=(y.imag * x.real)} {b=(y.real * x.imag)})
                in Refl


export
mult_associative : (Num t, Neg t)
    => {mult_assoc_t: {a,b,c:t} -> (a * b) * c = a * (b * c)}
    -> {plus_assoc_t: {a,b,c:t} -> (a + b) + c = a + (b + c)}
    -> {minus_assoc_t: {a,b,c:t} -> (a - b) - c = a - (b + c)}
    -> {plus_dist_t: {a,b,c:t} -> a * (b + c) = a * b + a * c}
    -> {minus_dist_t: {a,b,c:t} -> a * (b - c) = a * b - a * c}
    -> {plus_comm_t: {a,b:t} -> a + b = b + a}
    -> {x, y, z:Complex t}
    -> (x * y) * z = x * (y * z)
mult_associative = 
  rewrite (prf2 {xr=x.real, xi=x.imag, yr=y.real, yi=y.imag, zr=z.real, zi=z.imag})
    in rewrite prf1 in Refl
  where
    prf1 : ((x.real * ((y.real * z.imag) + (y.imag * z.real))) + (x.imag * ((y.real * z.real) - (y.imag * z.imag))))
             = ((((x.real * y.real) - (x.imag * y.imag)) * z.imag) + (((x.real * y.imag) + (x.imag * y.real)) * z.real))
    prf1 = ?pr1_rhs

    prf2 : {xr, xi, yr, yi, zr, zi : t}
        -> ((xr * ((yr * zr) - (yi * zi))) - (xi * ((yr * zi) + (yi * zr))))
           = ((((xr * yr) - (xi * yi)) * zr) - (((xr * yi) + (xi * yr)) * zi))
    prf2 = rewrite (minus_dist_t {a=xr, b=yr * zr, c=yi * zi})
            in rewrite (plus_dist_t {a=xi, b=yr * zi, c=yi * zr})
            in rewrite (q {a=xr * (yr * zr), b=xr * (yi * zi),
                           c=xi * (yr * zi), d=xi * (yi * zr) })
            in ?prf2_rhs
      where
        q : {a, b, c, d:t} -> (a - b) - (c + d) = (a - d) - (b + c)
        q = ?q





export
distributive : (Num t, Neg t)
    => {x, y:Complex t}
    -> {dist_t: {a,b,c:t} -> a * (b + c) = a * b + a * c}
    -> {plus_commu_t: {a,b:t} -> a + b = b + a}
    -> x * (y + z) = x * y + x * z
distributive = rewrite (dist_t {a=x.real} {b=y.real} {c=z.real})
            in rewrite (dist_t {a=x.imag} {b=y.imag} {c=z.imag})
            in rewrite (dist_t {a=x.real} {b=y.imag} {c=z.imag})
            in rewrite (dist_t {a=x.imag} {b=y.real} {c=z.real})
            in ?lhs_distributive



-- --------------------------------------------------------------------------

export
conjugate : Neg t => Complex t -> Complex t
conjugate x = MkComplex x.real (negate x.imag)


export
conjugate_distributive : (Num t, Neg t)
    => {x, y: Complex t}
    -> {pr: {a,b:t} -> negate (a + b) = negate a + negate b}
    -> conjugate (x + y) = conjugate x + conjugate y
conjugate_distributive = rewrite (pr {a =x.imag} {b=y.imag}) in Refl



-- --------------------------------------------------------------------------
-- vim: tw=80 sw=2 expandtab :
