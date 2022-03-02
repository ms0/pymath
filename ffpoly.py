__all__ = ['irreducibles','irreducibleg']

from conversions import isffield, xrange
from ffield import ffield
from poly import polynomial

def irreducibles(q,n) :
  """Return a tuple of all monic irreducible degree n polynomials over F;
  F is q if q is a finite field; else q must be a prime power, and F=ffield(q)."""
  return tuple(irreducibleg(q,n));

def irreducibleg(q,n) :
  """Generate lexicographically all monic irreducible degree n polynomials over F
  F is q if q is a finite field; else q must be a prime power, and F=ffield(q)."""
  if isffield(q) :
    F = q;
    q = F.q;
  else :
    F = ffield(q);
  for i in xrange(q**n) :
    poly = [];
    for k in range(n) :
      poly.append(i%q);
      i //= q;
    poly = polynomial(F(1),*map(F,reversed(poly)));
    if poly.isirreducible() : yield poly;
