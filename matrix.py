#matlab-style multidimensional arrays
#matrix elements can be any sort of interoperable numbers
#for example, matrices over a finite field can use elements from ffield.py

from __future__ import division

__all__ = ['matrix','bmatrix']

import sys
import types

try :
  from math import gcd
except Exception :
  def gcd(x,y) :
    """Return the [nonnegative] greatest common divisor of x and y"""
    while y :
      x,y = y, x%y;
    return abs(x);

from math import log

if sys.version_info[0] < 3 :

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,(int,long));

  def isreal(x) :
    """Return True iff a real number"""
    return isinstance(x,(int,long,float));

else :

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,int);

  def isreal(x) :
    """Return True iff a real number"""
    return isinstance(x,(int,float));

  xrange = range

def altabs(x) :
  try :
    return abs(x);
  except Exception :
    return 1 if x else 0;

class ParameterError(Exception) :
  pass

class Unimplemented(Exception) :
  pass

def islistlike(a) :
  """Return True iff a list or tuple"""
  return isinstance(a,(list,tuple));

def product(iterable,start=1) :
  """Return the product of start and the elements of the iterable"""
  for i in iterable :
    start *= i;
  return start;

def dot(v1,v2) :
  """Return the dot product of two vectors"""
  if len(v1) != len(v2) : raise ParameterError('vectors must have same length');
  s = 0;
  for i in xrange(len(v1)) :
    s += v1[i]*v2[i];
  return s;

def matmul(p,q,r,v1,v2) :
  """Multiply pxq array of elements v1 by qxr array of elements v2, result is pxr"""
  v = [0]*(p*r);
  for i in xrange(p) :
    for k in xrange(r) :
      v[i+k*p] = dot(v1[i::p],v2[k*q:(k+1)*q]);
  return v;

def listr(v) :    # output string for list, using str rather than repr
  return '[ '+', '.join(map(str,v))+' ]';

class matrix(object) :    # multidimensional array
  """Multidimensional array
2-D: matrix(nrows,ncolumns)
1-D (so nrows only), can be considered a column vector or a row vector

 An array is stored as a list v, so for dims = [A,B,C,D,...],
 M[a,b,c,d,...] = v[a+A*(b+B*(c+C*(d+D*...)))]
 so consecutive elements are down rows, then over columns, then ...

Instance variables:
  dims: a tuple giving the dimensions of the array
  tr or trace: the trace of the [square] matrix
  squeeze: an array with the same elements but all 1s in dims removed
  T or transpose: the transpose of the matrix [of dimension <= 2]
  H or conjugate_transpose: the Hermitian transpose of the matrix [dim <= 2]
  det or determinant: the determinant of the [square] matrix
  inverse: the inverse of the [square] matrix
  rank: the rank of the matrix (may be wrong if any float or complex elements)
Methods:
  __init__, __repr__, __str__, __getitem__,
  __bool__, __nonzero__, __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
  __neg__, __invert__, __iadd__, __add__, __radd__, __isub__, __sub__, __rsub__,
  __imul__, __mul__, __rmul__, __itruediv__, __idiv__, __truediv__, __div__

NOTE: a 1x1x1x...1 matrix is treated as a scalar [could even be no 1s]
NOTE: a list or tuple is coerced to a scalar or 1D matrix when multiplying with a matrix"""

  def __init__(self,*dims) :
    """Create a matrix
matrix(matrix_arg) makes a copy of matrix_arg
matrix(d1,d2,...,dk) or
matrix(d1,d2,...,dk,[one or prod(di) elements, column by column, ...])
makes a matrix with dimension d1 x d2 x ... x dk having elements all 0 or
all as specified in last arg
matrix([d1,d2,...dk]) same as matrix(d1,d2,...dk)
matrix([d1,d2,...dk],[one or prod(di)...]) also legal
matrix([d1,d2,...dk],one or prod(di) args to be elements) also legal
Elements are not checked for type, to allow for custom number types,
but, always use a list for specifying elements in this case,
to handle elements that look like lists (e.g., quaternions)
*** this implementation assumes addition is commutative!!! ***"""
    if not dims : raise ParameterError('requires some arguments');
    self.__dict__['_matrix__v'] = [];
    self.__dict__['_matrix__dims'] = [];
    if isinstance(dims[0],matrix) :
      if len(dims) != 1 : raise ParameterError('matrix arg must be only one');
      self.__dims[:] = dims[0].__dims;
      self.__v[:] = dims[0].__v;
      return;
    if isinstance(dims[0],bmatrix) :
      if len(dims) != 1 : raise ParameterError('bmatrix arg must be only one');
      self.__dims[:] = dims[0].dims;
      self.__v[:] = list(dims[0]);
      return;
    if islistlike(dims[0]) :
      v = dims[1] if len(dims) == 2 and islistlike(dims[1]) \
          else dims[1:] if dims[1:] else (0,);
      dims = dims[0];
    elif islistlike(dims[-1]) :
      v = dims[-1];
      dims = dims[0:-1];
    else :
      v = (0,);
    self.__v[:] = v;
    for n in dims :
      if not isint(n) or n <= 0 :
        raise TypeError('dimensions must be positive integers');
    self.__dims[:] = dims;
    if len(v) == 1 :
      self.__v[:] = v*product(dims);
    elif len(self.__v) != product(dims) :
      raise ParameterError('number of elements must match matrix dimensions');

  def __repr__(self) :
    return 'matrix('+repr(self.__dims)+','+repr(self.__v)+')';

  def __str__(self) :
    """Return a string showing the matrix in matrix format,
with each line fixing all but one dimension (varying the second or the only dimension),
with successive lines varying the remaining dimensions, earlier faster"""
    if len(self.__dims) <= 1 :
      return listr(self.__v);
    else :
      s = [];
      # iterate across all dimensions > 2!
      d = self.__dims[2:];
      c = [0]*len(d);
      rc = product(self.__dims[0:2]);
      n = len(self.__v) // rc;
      for i in xrange(n) :
        if n > 1 : s.append(str(tuple(c)) + ' :');
        m = self.__v[i*rc:(i+1)*rc];
        for r in xrange(self.__dims[0]) :
          s.append(listr(m[r::self.__dims[0]]));
        for j in xrange(len(c)) :
          c[j] = (c[j]+1) % d[j];
          if c[j] : break;
    return '\n'.join(s);

  #### comparison operators ####

  def __bool__(self) :
    """Return True iff any element is nonzero"""
    return any(self.__v);

  __nonzero__ = __bool__

  def __lt__(self,other) :
    """Return True iff each element of first array < corresponding element of the other"""
    if len(self.__v) == 1 :    #scalar
      return self.__v[0] < other;
    if not isinstance(other,matrix) or self.__dims != other.__dims :
      raise TypeError('only matrices of identical dimensions can be compared');
    for i in xrange(len(self.__v)) :
      if not self.__v[i] < other.__v[i] : return False;
    return True;

  def __le__(self,other) :
    """Return True iff each element of first array <= corresponding element of the other"""
    if len(self.__v) == 1 :    #scalar
      return self.__v[0] <= other;
    if not isinstance(other,matrix) or self.__dims != other.__dims :
      raise TypeError('only matrices of identical dimensions can be compared');
    for i in xrange(len(self.__v)) :
      if not self.__v[i] <= other.__v[i] : return False;
    return True;

  def __eq__(self,other) :
    """Return True iff each element of first array == corresponding element of the other"""
    if len(self.__v) == 1 :    #scalar
      return self.__v[0] == other;
    else :
      return isinstance(other,matrix) and \
        self.__dims == other.__dims and self.__v == other.__v;

  def __ne__(self,other) :
    """Return False iff each element of first array == corresponding element of the other"""
    return not self == other;

  def __ge__(self,other) :
    """Return True iff each element of first array >= corresponding element of the other"""
    if len(self.__v) == 1 :    # scalar
      return self.__v[0] >= other;
    if not isinstance(other,matrix) or self.__dims != other.__dims :
      raise TypeError('only matrices of identical dimensions can be compared');
    for i in xrange(len(self.__v)) :
      if not self.__v[i] >= other.__v[i] : return False;
    return True;

  def __gt__(self,other) :    
    """Return True iff each element of first array > corresponding element of the other"""
    if len(self.__v) == 1 :    # scalar
      return self.__v[0] > other;
    if not isinstance(other,matrix) or self.__dims != other.__dims :
      raise TypeError('only matrices of identical dimensions can be compared');
    for i in xrange(len(self.__v)) :
      if not self.__v[i] > other.__v[i] : return False;
    return True;


  def __neg__(self) :
    """Return the additive inverse of the array"""
    s = type(self)(self);
    for i in xrange(len(s.__v)) :
      s.__v[i] = -s.__v[i];
    return s;

  def __invert__(self) :
    """Apply ~ to each element of a copy of the array"""
    s = type(self)(self);
    for i in xrange(len(s.__v)) :
      s.__v[i] = ~s.__v[i];
    return s;


  def __iadd__(self, other) :
    """Add an array elementwise to this array, or,
if other is a scalar, add the scalar to each element of this array"""
    if isinstance(other,matrix) :
      if len(other.__v) == 1 :
        for i in xrange(len(self.__v)) :
          self.__v[i] += other.__v[0];
      elif other.__dims == self.__dims :
        for i in xrange(len(self.__v)) :
          self.__v[i] += other.__v[i];
      elif len(self.__v) == 1 :
        self.__dims[:] = other.__dims;
        self.__v[:],other = other.__v,self.__v[0];
        for i in xrange(len(self.__v)) :
          self.__v[i] += other;
      else : raise ParameterError('matrices must have same dimensions');
    else :        # scalar
      for i in xrange(len(self.__v)) :
        self.__v[i] += other;
    return self;

  def __add__(self, other) :
    """Return the elementwise sum of two arrays, or, if other is a scalar,
return a copy of the first array with each element incremented by the scalar"""
    a = type(self)(self);
    return a.__iadd__(other);

  __radd__ = __add__;


  def __isub__(self, other) :
    """Subtract an array elementwise from this array, or,
if other is a scalar, subtract the scalar from each element of this array"""
    if isinstance(other,matrix) :
      if len(other.__v) == 1 :
        for i in xrange(len(self.__v)) :
          self.__v[i] -= other.__v[0];
      elif other.__dims == self.__dims :
        for i in xrange(len(self.__v)) :
          self.__v[i] -= other.__v[i];
      else : raise ParameterError('matrices must have same dimensions');
    else :                # scalar
      for i in xrange(len(self.__v)) :
        self.__v[i] -= other;

    return self;

  def __sub__(self, other) :
    """Return the elementwise difference of two arrays, or, if other is a scalar,
return a copy of the first array with each element decremented by the scalar"""
    a = type(self)(self);
    return a.__isub__(other);

  def __rsub__(self, other) :
    """Return -self+other"""
    return self.__neg__().__add__(other);

  def __imul__(self,other) :
    """Update self to be the product of self and other as follows:
any * scalar :  scalar multiply
1D * 1D:  dot product (sum of the elementwise products)
2D * 2D:  matrix multiply
2D * 1D  or  1D * 2D:  treat vector as row or column as appropriate"""
    if isinstance(other,matrix) :
      if len(other.__v) == 1 :           # other is scalar
        for i in xrange(len(self.__v)) :
          self.__v[i] *= other.__v[0];   # assume a *= b means a = a*b
      elif len(self.__v) == 1 :          # self is scalar
        c = self.__v[0];
        self.__v[:] = other.__v;
        for i in xrange(len(self.__v)) :
          self.__v[i] = c*other.__v[i];  # allows non-commutativity
      elif len(self.__dims) == 1 :       # self is 1D matrix
        if len(other.__dims) == 1 :        # 1D x 1D
          if len(self.__v) != len(other.__v) :
            raise ParameterError('vectors must have same length');
          self.__dims[:] = [];
          self.__v[:] = [dot(self.__v,other.__v)];
        elif len(other.__dims) == 2 :      # 1D x 2D
          if self.__dims[0] != other.__dims[0] :
            raise ParameterError('inner dimensions must agree');
          self.__v[:] = matmul(1, other.__dims[0], other.__dims[1], 
                               self.__v, other.__v);
          self.__dims[0] = other.__dims[1];
        else : raise TypeError('only matrices can be multiplied');
      elif len(self.__dims) == 2 :       # self is 2D matrix
        if len(other.__dims) <= 2 :        # 2D x 1D or 2D x 2D
          if self.__dims[1] != other.__dims[0] :
            raise ParameterError('inner dimensions must agree');
          self.__dims[1] = 1 if len(other.__dims) < 2 else other.__dims[1];
          self.__v[:] = matmul(self.__dims[0], other.__dims[0], self.__dims[1],
                               self.__v, other.__v);
          if len(other.__dims) < 2 : del self.__dims[1];   # preserve vectorness
        else : raise TypeError('only matrices can be multiplied');
      else : raise TypeError('only matrices can be multiplied');
    elif islistlike(other) :
      return self.__imul__(type(self)(len(other),other));
    else :    # matrix * scalar
      for i in xrange(len(self.__v)) :
        self.__v[i] *= other;
    return self;

  def __mul__(self,other) :
    """Return the product of the two args, as for __imul__"""
    return type(self)(self).__imul__(other);

  def __rmul__(self,other) :    # can only be scalar*matrix or vector*matrix
    """Return the product of the two args, as for __imul__"""
    if islistlike(other) :
      return type(self)(len(other),other).__imul__(self);
    b = type(self)(self);
    for i in xrange(len(b.__v)) :
      b.__v[i] = other*b.__v[i];
    return b;

  def _scalardiv(self,b) :
    """Divide self by scalar b"""
    for i in xrange(len(self.__v)) :
      self.__v[i] /= b ;
    return self;

  def __itruediv__(self,other) :
    """Divide self by other"""
    if isinstance(other,matrix) :
      if len(other.__v) == 1 :
        return self._scalardiv(other.__v[0]);
      if len(self.__dims) == 2 and self.__dims[0] == self.__dims[1] :
        return self.__imul__(other**-1);
      raise TypeError('only square matrices can be divisors');
    elif islistlike(other) :
      if len(other) == 1 :
        return self._scalardiv(other[0]);
      raise TypeError('only square matrices can be divisors');
    return self._scalardiv(other);

  __idiv__ = __itruediv__;

  def __truediv__(self,other) :
    """Return the quotient self/other"""
    return type(self)(self).__itruediv__(other);

  __div__ = __truediv__;

  def __rtruediv__(self,other) :
    """Return the product other*self**-1"""
    return other*self.inverse;

  __rdiv__ = __rtruediv__;

  def __ipow__(self,x) :
    """Raise a scalar to a power or a square matrix to an integer power"""
    # compute self**x; self must be square matrix and x must be integer
    # if x < 0, self must be invertible
    if len(self.__v) == 1 :    # scalar
      self.__v[0]**=x;
      return self;
    n = self.__dims[0];    # number of rows
    if len(self.__dims) != 2 or n != self.__dims[1] :
      raise TypeError('base must be square matrix') ;
    e = int(x);
    if e != x : raise TypeError('requires integer exponent');
    if e < 0 :
      m = self.inverse;
      e = -e;
    else :
      m = type(self)(self);
    v = [0]*(n*n);
    v[0::(n+1)] = (1,)*n;
    self.__v[:] = v;
    while e :
      if e&1 : self *= m;
      e >>= 1;
      if not e : break;
      m *= m;
    return self;

  def __pow__(self,x) :
    """Return the exponentiation of a scalar to a power or a square matrix to an integer power"""
    return type(self)(self).__ipow__(x);

  def __rpow__(self,b) :
    """Return scalar b to a square matrix power"""
    # base ** matrix
    if len(self.__v) == 1 :
      return type(self)(self.__dims,b**self.__v[0]);
    n = self.__dims[0];
    if len(self.__dims) != 2 or n != self.__dims[1] :
      return TypeError('exponent must be square matrix');
    if not isreal(b) :
      approximate = lambda x: x.significate(16);
      logb = approximate(b.log());    # an exception here is legit
    elif b > 0 :
      logb = log(b);
      approximate = None;
    else :
      return TypeError('base must be positive real');
    P = logb*self;
    S = self.Identity(n);
    M = self.Identity(n);
    for x in xrange(1,10001) :
      M *= P;
      M /= x;
      v = S.__v[:];
      S += M;
      if approximate :
        M.mapply(approximate);
        S.mapply(approximate);
      if v == S.__v : break;
    return S;

  def __abs__(self) :
    """Return the square root of the sum of the absolute squares of the array elements"""
    s = 0;
    for x in self.__v :
      s += x*x.conjugate();
    return s**.5;

  def __len__(self) :
    """Return the number of elements in the array"""
    return len(self.__v);

# we have to be able to do multi-dimensional indexing
# for slices, key is type slice, with attributes start stop step

  def __getitem__(self,key) :
    """Return an item or slice of the array;
if the specified slice or index is singly dimensioned, but the array isn't,
treat the array as a list of its elements in storage order"""
    if not isinstance(key,tuple) :
      v = self.__v[key];    # linear indexing always allowed
      if isint(key) or not v or len(self.__dims) > 1 :
        # if key is just a linear index, or
        #    key is a slice with no elements, or
        #    have multiple dimensions, then return the element or element list
        return v;
      # return the submatrix...
      return type(self)([len(v)] if self.__dims else [] ,v);
    if len(key) != len(self.__dims) :
      raise ParameterError('length of index list must be number of dimensions');
    key = list(key);    # so can modify it
    # figure out dims of result, which depends on slices
    dims = [];
    single = True;
    for i in xrange(len(self.__dims)) :
      if isinstance(key[i],slice) :
        key[i] = key[i].indices(self.__dims[i]);
        dim = len(xrange(*key[i]));
        if not dim :
          raise IndexError('no items selected');
        dims.append(dim);
        single = False;
      elif isint(key[i]) :
        if not 0 <= key[i] < self.__dims[i] :
          raise IndexError('index out of range');
        key[i] = (key[i],);
        dims.append(1);
      else :
        raise TypeError('index type unsupported');
    if single :
      s = 0
      for i in reversed(xrange(len(key))) :
        s = s*self.__dims[i] + key[i][0];
      return self.__v[s];
    # must return a submatrix...
    v = [];
    x = [0]*len(dims);
    while True :
      s = 0;
      for i in reversed(xrange(len(key))) :
        if len(key[i]) == 1 :
          s = s*self.__dims[i] + key[i][0];
        else :
          s = s*self.__dims[i] + list(xrange(*key[i]))[x[i]];
      v.append(self.__v[s]);
      for i in xrange(len(dims)) :
        x[i] = (x[i]+1)%dims[i];
        if x[i] : break;
      else : break;
    for i in reversed(xrange(len(dims))) :
      if len(key[i]) == 1 : del dims[i];
    return type(self)(dims,v);


  def __setitem__(self,key,value) :
    """Set an item or slice of the array, interpreting key as for __getitem__;
when setting a slice, value must have length matching size of slice"""
    if not isinstance(key,tuple) :
      if isinstance(key,slice) :
        k = key.indices(len(self.__v));
        dim = len(xrange(*k));
        if isreal(value) :
          for i in xrange(*k) : self.__v[i] = value;
          return;
        if len(value) != dim :
          raise TypeError('value must have same length as slice');
      self.__v[key] = value;    # linear indexing always allowed
      return;
    if len(key) != len(self.__dims) :
      raise ParameterError('length of index list must be number of dimensions');
    # figure out dims of result, which depends on slices
    key = list(key);    # so can modify it
    # figure out dims of result, which depends on slices
    dims = [];
    single = True;
    for i in xrange(len(self.__dims)) :
      if isinstance(key[i],slice) :
        key[i] = key[i].indices(self.__dims[i]);
        dim = len(xrange(*key[i]));
        dims.append(dim);
        single = False;
      elif isint(key[i]) :
        if not 0 <= key[i] < self.__dims[i] :
          raise IndexError('index out of range');
        key[i] = (key[i],);
        dims.append(1);
      else :
        raise TypeError('index type unsupported');
    if single :
      s = 0
      for i in reversed(xrange(len(key))) :
        s = s*self.__dims[i] + key[i][0];
      self.__v[s] = value;
      return;
    # must set a submatrix...
    pdims = product(dims);
    if not isreal(value) and pdims != len(value) :
      raise TypeError('value must have same length as slice');
    x = [0]*len(dims);
    for j in xrange(pdims) :
      s = 0;
      for i in reversed(xrange(len(key))) :
        if len(key[i]) == 1 :
          s = s*self.__dims[i] + key[i][0];
        else :
          s = s*self.__dims[i] + list(xrange(*key[i]))[x[i]];
      self.__v[s] = value if isreal(value) else value[j];
      for i in xrange(len(dims)) :
        x[i] = (x[i]+1)%dims[i];
        if x[i] : break;
      else : break;
    for i in reversed(xrange(len(dims))) :
      if len(key[i]) == 1 : del dims[i];
    if isinstance(value,matrix) and dims != value.__dims :
      raise UserWarning('value and slice dimensions differ');
    return;

  @property
  def conjugate(self) :
    """conjugate"""
    return self.mapped(lambda x:x.conjugate());

  @property
  def dims(self) :
    """tuple of dimensions"""
    return tuple(self.__dims);

  @property
  def tr(self) :
    """trace"""
    if len(self.__v) == 1 :
      return self.__v[0];
    n = self.__dims[0];
    if len(self.__dims) != 2 or n != self.__dims[1] :
      raise AttributeError('trace arequires square matrix') ;
    return sum(self.__v[0::(n+1)]);

  @property
  def trace(self) :
    """trace"""
    return self.tr;

  @property
  def squeeze(self) :
    """squeeze (length 1 dimensions elided)"""
    s = type(self)(self);
    for i in reversed(xrange(len(s.__dims))) :
      if s.__dims[i] == 1 : del s.__dims[i];
    return s;

  @property
  def T(self) :
    """transpose"""
    # if 2D, return transposed matrix
    # if 1D, return copy of self
    # else, raise exception
    s = type(self)(self);
    if len(s.__dims) == 2 :
      s.__dims[:] = self.__dims[1],self.__dims[0];
      for c in xrange(s.__dims[1]) :    # column of the result
        # copy a row to a column:
        s.__v[s.__dims[0]*c:s.__dims[0]*(c+1)] = self.__v[c::self.__dims[0]];
    elif len(s.__dims) > 2 :
      raise AttributeError('transpose not defined for >2D matrices');
    return s;

  @property
  def transpose(self) :
    """transpose"""
    return self.T;

  @property
  def H(self) :
    """conjugate transpose"""
    s = self.transpose;
    s.map(lambda x:x.conjugate());
    return s;

  @property
  def conjugate_transpose(self) :
    """conjugate transpose"""
    return self.H;

  @property
  def rank(self) :
    """rank"""
    if len(self.__v) <= 1 :
      return 1-(not self.__v[0]);
    n = self.__dims[0];    # number of rows
    if len(self.__dims) != 2 :
      if len(self.__dims) == 1 :
        return 0 + any(self.__v);
      raise TypeError('requires matrix') ;
    integral = 1;
    v = self.__v[:];
    for x in v :
      if not isint(x) :
        integral = 0;
        break;
    nc = self.__dims[1];    # number of columns
    rank = 0;
    rows = list(xrange(n));
    if integral :
      for c in xrange(nc) :    # for each column
        if not rows : break;
        x = float('inf');
        for r in rows :    # find pivot row (smallest nonzero pivot element)
          a = abs(v[r+n*c]);
          if a and a < x :
            x = a;
            pr = r;
        if isint(x) :
          rank += 1;
          x = v[pr+n*c];
          rx = rows.index(pr);
          del rows[rx];
          for r in rows :
            a = v[r+n*c];
            g = gcd(a,x);
            mx = a//g;
            ma = x//g;
            for cc in xrange(c+1,nc) :
              v[r+n*cc] = ma*v[r+n*cc] - mx*v[pr+n*cc];
    else :
      for c in xrange(nc) :    # for each column
        if not rows : break;
        x = 0;
        for r in rows :    # find pivot row (largest pivot element)
          a = altabs(v[r+n*c]);
          if a > x :
            x = a;
            pr = r;
        if x :
          rank += 1;
          x = v[pr+n*c];
          for pc in xrange(c+1,nc) :
            v[pr+n*pc] /= x;
          rx = rows.index(pr);
          del rows[rx];
          for r in rows :
            a = v[r+n*c];
            for cc in xrange(c+1,nc) :
              v[r+n*cc] -= a*v[pr+n*cc];
    return rank;

  @property
  def det(self) :
    """determinant"""
    if len(self.__v) <= 1 :
      return self.__v[0];
    n = self.__dims[0];
    if len(self.__dims) != 2 or n != self.__dims[1] :
      raise AttributeError('rank requires square matrix') ;
    integral = 1;
    v = self.__v[:];
    for x in v :
      if not isint(x) :
        integral = 0;
        break;
    if integral :
      d = 1;    # numerator
      dd = 1;   # denominator
      rows = list(xrange(n));
      for c in xrange(n-1) :    # for each column
        x = float('inf');
        for r in rows :    # find pivot row (smallest nonzero pivot element)
          a = abs(v[r+n*c]);
          if a and a < x :
            x = a;
            pr = r;
        if not isint(x) : return 0;
        x = v[pr+n*c];
        d *= x;
        rx = rows.index(pr);
        if rx & 1 :
          d = -d;
        del rows[rx];
        for r in rows :
          a = v[r+n*c];
          g = gcd(a,x);
          mx = a//g;
          ma = x//g;
          dd *= ma;
          for cc in xrange(c+1,n) :
            v[r+n*cc] = ma*v[r+n*cc] - mx*v[pr+n*cc];
      return d*v[rows[0]+n*(n-1)]//dd;
    d = 1;
    rows = list(xrange(n));
    for c in xrange(n-1) :    # for each column
      x = 0;
      for r in rows :    # find pivot row (largest pivot element)
        a = altabs(v[r+n*c]);
        if a > x :
          x = a;
          pr = r;
      if not x : return 0;
      x = v[pr+n*c];
      d *= x;
      for pc in xrange(c+1,n) :
        v[pr+n*pc] /= x;
      rx = rows.index(pr);
      if rx & 1 :
        d = -d;
      del rows[rx];
      for r in rows :
        a = v[r+n*c];
        for cc in xrange(c+1,n) :
          v[r+n*cc] -= a*v[pr+n*cc];
    return d*v[rows[0]+n*(n-1)];

  @property
  def determinant(self) :
    return self.det;

  @property
  def inverse(self) :
    """inverse"""
    if len(self.__v) <= 1 :
      s = type(self)(self);
      s.__v[0] = 1/s.__v[0];
      return s;
    n = self.__dims[0];
    if len(self.__dims) != 2 or n != self.__dims[1] :
      raise AttributeError('requires square matrix') ;
    n2 = n*n;
    v = [0]*n2;
    v[0::(n+1)] = (1,)*n;
    v += self.__v;
    for c in xrange(n) :
      x = 0;
      for r in xrange(c,n) :
        a = altabs(v[n2+r+n*c]);
        if a > x :
          x = a;
          pr = r;
      if not x : raise ZeroDivisionError('matrix not invertible');
      if pr != c : v[c::n],v[pr::n] = v[pr::n],v[c::n];
      x = v[n2+c*(n+1)];
      if x != 1 :
        y = 1/x;
        for cc in xrange(2*n) : v[c+n*cc] = y*v[c+n*cc];
      for r in xrange(c+1,n) :
        x = v[n2+r+n*c];
        for cc in xrange(2*n) :
          v[r+n*cc] -= x*v[c+n*cc];
    for c in reversed(xrange(1,n)) :
      for r in xrange(0,c) :
        x = v[n2+r+n*c];
        for cc in xrange(n) :
          v[r+n*cc] -= x*v[c+n*cc];
    return type(self)(n,n,v[0:n2]);

  def reshape(self,*dims) :
    """Return a new array with the same elements but different dimensions,
one dimension may be left unspecified (0 or None) and will be filled in,
the product of the new dimensions must equal the product of the old dimensions"""
    if len(dims) == 1 and islistlike(dims[0]) : dims = dims[0];
    for d in dims :
      if (not isint(d) or d < 0) and d != None :
        raise TypeError('dimensions must be positive integers');
    x = -1;
    for i in xrange(len(dims)) :
      if not dims[i] :
        if x < 0 :
          dims = list(dims);
          x = i;
          dims[x] = 1;    # will be replaced
        else :
          raise TypeError('at most one dimension can be unspecified');
    p = product(dims);
    q,r = divmod(len(self.__v),p);
    if r :
      raise ParameterError('desired dimensions not possible');
    if x < 0 :
      if q != 1 :
        raise ParameterError('desired dimensions not possible');
    else :
      dims[x] = q;
    return type(self)(dims,self.__v);

  def sum(self,*d) :
    """Return the sum of the array elements"""
    if d : raise NotImplementedError;
    return sum(self.__v);

  def product(self,*d) :
    """Return the product of the array elements"""
    if d : raise NotImplementedError;
    return product(self.__v);

  def max(self,*d) :
    """Return the max of the array elements"""
    if d : raise NotImplementedError;
    return max(self.__v);

  def min(self,*d) :
    """Return the min of the array elements"""
    if d : raise NotImplementedError;
    return min(self.__v);

  def median(self,*d) :
    """Return the median of the array elements"""
    if d : raise NotImplementedError;
    s = sorted(self.__v);
    z = len(s);
    if not z : raise ZeroDivisionError;
    return s[z//2] if z&1 else (s[z//2-1]+s[z//2])/2;

  def mean(self,*d) :
    """Return the mean of the array elements"""
    if d : raise NotImplementedError;
    return sum(self.__v) / len(self.__v);

  def map(self,map,*d) :
    """Apply map to each element of the array"""
    # with no additional args, apply map to each element
    if not d :
      for i in xrange(len(self.__v)) :
        self.__v[i] = map(self.__v[i]);
      return;
   # with one additional nonnegative integer arg, apply map to each vector
    #  along dimension d[0], and replace that vector with the result
    # with two ania, apply map to each 2D matrix along d[0] and d[1], ...
    raise NotImplementedError;

  mapply = map    # for backward compatiblity

  def mapped(m,map,*d) :
    """Return a copy of m with map applied to each element"""
    m = type(m)(m);
    m.map(map,*d);
    return m;

  mapplied = mapped    # for backward compatibility

  @staticmethod
  def Identity(n,m=1) :
    """Return an nxn identity matrix multiplied by the scalar m"""
    v = [m*0]*(n*n);    # coerce 0 to same type as m
    v[0::(n+1)] = (m,)*n;
    I = matrix(n,n,v);
    return I;

  @staticmethod
  def circulant(row) :
    """Return a circulant matrix given its first row"""
    n = len(row);
    M = matrix(n,n);
    for r in range(n) :
      M[r,:r] = row[n-r:];
      M[r,r:] = row[:n-r];
    return M;

################################################################
# boolean [binary] matrices

def parity(iterable,start=0) :
  """Return parity of an integer or xor of an iterable, xor'd with start"""
  if isint(iterable) :
    return bin(iterable).count('1')&1^start;
  for i in iterable :
    start ^= i;
  return start;

_v = '_bmatrix__v'

class bmatrix(object) :

  """boolean matrix"""

  def __init__(self,*dims) :
    """Create a boolean matrix
bmatrix(bmatrix_arg) makes a copy of bmatrix_arg
bmatrix(matrix_arg) make a bmatrix of same dimensions,
replacing each element with whether or not it evaluates true, i.e. 1 if x else 0
bmatrix(d1,d2,...,dk) or
bmatrix(d1,d2,...,dk,[one or prod(di) elements, column by column, ...])
makes a bmatrix with dimension d1 x d2 x ... x dk having elements all 0 or
all as specified in last arg, treated as binary with lsb first
bmatrix([d1,d2,...dk]) same as bmatrix(d1,d2,...dk)
bmatrix([d1,d2,...dk],[one or prod(di)...]) also legal
bmatrix([d1,d2,...dk],one or prod(di) args to be elements) also legal"""
    if not dims : raise ParameterError('requires some arguments');
    self.__dict__['_bmatrix__dims'] = [];
    if isinstance(dims[0],bmatrix) :
      if len(dims) != 1 : raise ParameterError('bmatrix arg must be only one');
      self.__dims[:] = dims[0].__dims;
      self.__dict__[_v] = dims[0].__v;
      return;
    if isinstance(dims[0],matrix) :
      if len(dims) != 1 : raise ParameterError('matrix arg must be only one');
      self.__dims[:] = dims[0].dims;
      v = 0;
      for x in reversed(dims[0]) : v = (v<<1)|(1 if x else 0);
      self.__dict__[_v] = v;
      return;
    if islistlike(dims[0]) :
      w = dims[1] if len(dims) == 2 and islistlike(dims[1]) \
          else dims[1:] if dims[1:] else (0,);
      dims = dims[0];
    elif islistlike(dims[-1]) :
      w = dims[-1];
      dims = dims[0:-1];
    else :
      w = (0,);
    for n in dims :
      if not isint(n) or n <= 0 :
        raise TypeError('dimensions must be positive integers');
    self.__dims[:] = dims;
    p = product(dims);
    if len(w) == product(dims) :
      v = 0;
      for x in reversed(w) : v = (v<<1)|(1 if x else 0);
      self.__dict__[_v] = v;
    elif len(w) == 1 and isint(w[0]) and -1<<p < w[0] < 1<<p:
      self.__dict__[_v] = w[0] & ((1<<p)-1);
    else :
      raise ParameterError('number of elements must match bmatrix dimensions');

  def __repr__(self) :
    return 'bmatrix('+repr(self.__dims)+',0x%x)'%(self.__v);

  def __str__(self) :
    """Return a string showing the matrix in matrix format,
with each line fixing all but one dimension (varying the second or the only dimension),
with successive lines varying the remaining dimensions, earlier faster"""
    if len(self.__dims) <= 1 :
      if not self.__dims : return(str(self.__v));
      return '['+format(self.__v,'0%db'%(self.__dims[0]))[::-1]+']';
    else :
      s = [];
      # iterate across all dimensions > 2!
      d = self.__dims[2:];
      q = [0]*len(d);
      rc = product(self.__dims[0:2]);
      n = product(self.__dims[2:]);
      nr = self.__dims[0];
      nc = self.__dims[1];
      m = (1<<rc)-1;
      f = '0%db'%(nc);
      for i in xrange(n) :
        if n > 1 : s.append(str(tuple(q)) + ' :');
        v = (self.__v >> i*rc)&m;
        for r in xrange(nr) :
          b = 0;
          for c in xrange(nc) :
            b = 2*b|(v>>(nr*c+r))&1;
          s.append('['+format(b,f)+']');
        for j in xrange(len(q)) :
          q[j] = (q[j]+1) % d[j];
          if q[j] : break;
    return '\n'.join(s);

  def __len__(self) :
    return product(self.__dims);

  def __eq__(self,other) :
    """Return True iff each element of first array == corresponding element of the other"""
    return isinstance(other,bmatrix) and self.__v == other.__v and (
      self.__dims == other.__dims or 1 == len(self) == len(other));

  def __ne__(self,other) :
    """Return False iff each element of first array == corresponding element of the other"""
    return not self == other;

  def __lt__(self,other) :
    raise TypeError('no ordering relation is defined for bmatrices');

  __le__ = __ge__ = __gt__ = __lt__

  def __getitem__(self,key) :
    """Return an item or slice of the array;
if the specified slice or index is singly dimensioned, but the array isn't,
treat the array as a list of its elements in storage order"""
    if not isinstance(key,tuple) :
      # linear indexing always allowed
      n = len(self);
      if isint(key) :
        if 0 <= key < n :
          return (self.__v >> key) & 1;
        elif -n <= key < 0 :
          return (self.__v >> (key+n)) & 1;
        else :
          raise IndexError('index out of range');
      elif isinstance(key,slice) :
        v = 0;
        c = 0;
        for k in reversed(xrange(*key.indices(n))) :
          v = 2*v+((self.__v>>k)&1);
          c += 1;
        return type(self)((c,),v) if c > 0 else [];
      else :
        return IndexError('index neither int nor slice');
    if len(key) != len(self.__dims) :
      raise ParameterError('length of index list must be number of dimensions');
    key = list(key);    # so can modify it
    # figure out dims of result, which depends on slices
    dims = [];
    single = True;
    for i in xrange(len(self.__dims)) :
      if isinstance(key[i],slice) :
        key[i] = key[i].indices(self.__dims[i]);
        dim = len(xrange(*key[i]));
        if not dim :
          raise IndexError('no items selected');
        dims.append(dim);
        single = False;
      elif isint(key[i]) :
        if not 0 <= key[i] < self.__dims[i] :
          raise IndexError('index out of range');
        key[i] = (key[i],);
        dims.append(1);
      else :
        raise TypeError('index type unsupported');
    if single :
      s = 0
      for i in reversed(xrange(len(key))) :
        s = s*self.__dims[i] + key[i][0];
      return (self.__v>>s)&1;
    # must return a submatrix...
    v = 0;
    x = [0]*len(dims);
    while True :
      s = 0;
      for i in reversed(xrange(len(key))) :
        if len(key[i]) == 1 :
          s = s*self.__dims[i] + key[i][0];
        else :
          s = s*self.__dims[i] + list(xrange(*key[i]))[x[i]];
      v = 2*v+self[s];
      for i in xrange(len(dims)) :
        x[i] = (x[i]+1)%dims[i];
        if x[i] : break;
      else : break;
    for i in reversed(xrange(len(dims))) :
      if len(key[i]) == 1 : del dims[i];
    d = product(dims);
    rv = 0;
    for i in xrange(d) :
      rv = 2*rv|(v>>i)&1;
    return type(self)(dims,rv);


  def __setitem__(self,key,value) :
    """Set an item or slice of the array, interpreting key as for __getitem__;
when setting a slice, value must have length matching size of slice"""
    n = product(self.__dims);
    if not isinstance(key,tuple) :
      # linear indexing always allowed
      if isinstance(key,slice) :
        k = key.indices(n);
        dim = len(xrange(*k));
        if isint(value) :
          if not(0 <= value < 1<<dim or -1<<dim < value < 0) :
            raise TypeError('value must have same length as slice');
        elif isinstance(value,bmatrix) :
          if len(value) != dim :
            raise TypeError('value must have same length as slice');
          value = value.__v;
        else :
          raise TypeError('value must be int or bmatrix');
        for i in xrange(*k) :
          self[i] = value&1;
          value >>= 1;
        return;
      if -n <= key < 0 : key += n;
      if not 0 <= key < n :
        raise IndexError('index out of range');
      if isint(value) :
        if not -2 <= value < 2 :
          raise TypeError('integer value must be a bit');
        value &= 1;
      if value : self.__dict__[_v] |= 1<<key;
      else : self.__dict__[_v] &= ~(1<<key);
      return;
    if len(key) != len(self.__dims) :
      raise ParameterError('length of index list must be number of dimensions');
    # figure out dims of result, which depends on slices
    key = list(key);    # so can modify it
    # figure out dims of result, which depends on slices
    dims = [];
    single = True;
    for i in xrange(len(self.__dims)) :
      if isinstance(key[i],slice) :
        key[i] = key[i].indices(self.__dims[i]);
        dim = len(xrange(*key[i]));
        dims.append(dim);
        single = False;
      elif isint(key[i]) :
        if not 0 <= key[i] < self.__dims[i] :
          raise IndexError('index out of range');
        key[i] = (key[i],);
        dims.append(1);
      else :
        raise TypeError('index type unsupported');
    if single :
      s = 0
      for i in reversed(xrange(len(key))) :
        s = s*self.__dims[i] + key[i][0];
      self[s] = value;
      return;
    # must set a submatrix...
    pdims = product(dims);
    if isint(value) :
      if not(0 <= value < 1<<pdims or -1<<pdims < value < 0) :
        raise TypeError('value must have same length as slice');
    elif pdims != len(value) :
      raise TypeError('value must have same length as slice');
    x = [0]*len(dims);
    for j in xrange(pdims) :
      s = 0;
      for i in reversed(xrange(len(key))) :
        if len(key[i]) == 1 :
          s = s*self.__dims[i] + key[i][0];
        else :
          s = s*self.__dims[i] + tuple(xrange(*key[i]))[x[i]];
      self[s] = (value>>j)&1 if isint(value) else value[j];
      for i in xrange(len(dims)) :
        x[i] = (x[i]+1)%dims[i];
        if x[i] : break;
      else : break;
    for i in reversed(xrange(len(dims))) :
      if len(key[i]) == 1 : del dims[i];
    if isinstance(value,bmatrix) and dims != value.__dims :
      raise UserWarning('value and slice dimensions differ');
    return;

  @property
  def conjugate(self) :
    """conjugate"""
    return type(self)(self);

  @property
  def dims(self) :
    """tuple of dimensions"""
    return tuple(self.__dims);

  @property
  def tr(self) :
    """trace"""
    if len(self) == 1 :
      return self.__v;
    n = self.__dims[0];
    if len(self.__dims) != 2 or n != self.__dims[1] :
      raise AttributeError('trace requires square bmatrix') ;
    return parity(self[0::(n+1)]);

  @property
  def trace(self) :
    """trace"""
    return self.tr;

  @property
  def squeeze(self) :
    """squeeze (length 1 dimensions elided)"""
    s = type(self)(self);
    for i in reversed(xrange(len(s.__dims))) :
      if s.__dims[i] == 1 : del s.__dims[i];
    return s;

  @property
  def T(self) :
    """transpose"""
    # if 2D, return transposed matrix
    # if 1D, return self
    # else, raise exception
    if len(self.__dims) == 2 :
      rows,cols = self.__dims;
      return type(self)((cols,rows),self.bT(rows,cols,self.__v));
    if len(self.__dims) <= 1 :
      return type(self)(self);
    raise AttributeError('transpose not defined for >2D bmatrices');

  @property
  def transpose(self) :
    """transpose"""
    return self.T;

  @property
  def H(self) :
    """conjugate transpose"""
    return self.T;

  @property
  def conjugate_transpose(self) :
    """conjugate transpose"""
    return self.T;

  @property
  def det(self) :
    """determinant"""
    if len(self) == 1 :
      return self[0];
    n = self.__dims[0];
    if len(self.__dims) != 2 or n != self.__dims[1] :
      raise TypeError('requires square bmatrix') ;
    v = self.__v;
    m = (1<<n)-1;    # mask of column
    for r in xrange(n) :
      rv = 0;
      b = 1<<r;    # row bit
      for c in xrange(r,n) :    # find pivot column
        cv = (v>>n*c)&m;
        if b&cv :
          if rv :
            v ^= rv<<n*c;
          else :
            if r != c : 
              # exchange this column with column r
              x = cv ^ (v>>n*r)&m;
              v ^= (x << n*r) ^ (x << n*c);
            rv = cv;
      if not rv : return 0;
    return 1;

  @property
  def determinant(self) :
    """determinant"""
    return self.det;

  @property
  def transpose(self) :
    return self.T;

  @property
  def rank(self) :
    """rank"""
    if len(self) == 1 :
      return self[0];
    n = self.__dims[0];    # number of rows
    if len(self.__dims) != 2 :
      if len(self.__dims) == 1 :
        return 1-(not self.__v);
      raise TypeError('requires bmatrix') ;
    nc = self.__dims[1];   # number of columns
    v = self.__v;
    m = (1<<n)-1;    # mask of column
    rank = 0;
    for r in xrange(n) :
      rv = 0;
      b = 1<<r;    # row bit
      for c in xrange(rank,nc) :    # find pivot column
        cv = (v>>n*c)&m;
        if b&cv :
          if rv :
            v ^= rv<<n*c;
          else :
            if rank != c : 
              # exchange this column with column rank
              x = cv ^ (v>>n*rank)&m;
              v ^= (x << n*rank) ^ (x << n*c);
            rv = cv;
      if rv : rank += 1;
    return rank;

  @property
  def inverse(self) :
    """inverse"""
    if len(self) == 1 :
      s = type(self)(self);
      if not s[0] :
        raise ZeroDivisionError('bmatrix not invertible');
      return s;
    n = self.__dims[0];
    if len(self.__dims) != 2 or n != self.__dims[1] :
      raise AttributeError('requires square bmatrix') ;
    w = 1;    # make identity
    for i in xrange(n-1) :
      w = (w<<(n+1))|1;
    v = self.__v;
    m = (1<<n)-1;    # mask of column
    for r in xrange(n) :    # for each row
      rv = 0;
      b = 1<<r;    # row bit
      for c in xrange(r,n) :    # find pivot column
        cv = (v>>n*c)&m;
        if b&cv :
          if rv :
            v ^= rv<<n*c;
            w ^= rw<<n*c;
          else :
            if r != c : 
              # exchange this column with column r
              x = cv ^ (v>>n*r)&m;
              v ^= (x << n*r) ^ (x << n*c);
              x = ((w>>n*c) ^ (w>>n*r)) & m;
              w ^= (x << n*r) ^ (x << n*c);
            rv = cv;
            rw = (w>>n*r)&m;
      if not rv : raise ZeroDivisionError('bmatrix not invertible');
    for r in reversed(xrange(1,n)) :
      rw = (w>>n*r)&m;
      for c in xrange(r) :
        if (v>>(n*c+r))&1 :
          w ^= rw<<n*c;
    return type(self)((n,n),w);

  @property
  def _bits(self) :
    """bmatrix as a binary number with lsb being first entry"""
    return self.__v;

  def reshape(self,*dims) :
    """Return a new array with the same elements but different dimensions,
one dimension may be left unspecified (0 or None) and will be filled in,
the product of the new dimensions must equal the product of the old dimensions"""
    if len(dims) == 1 and islistlike(dims[0]) : dims = dims[0];
    for d in dims :
      if (not isint(d) or d < 0) and d != None:
        raise TypeError('dimensions must be positive integers');
    x = -1;
    for i in xrange(len(dims)) :
      if not dims[i] :
        if x < 0 :
          dims = list(dims);
          x = i;
          dims[x] = 1;    # will be replaced
        else :
          raise TypeError('at most one dimension can be unspecified');
    p = product(dims);
    q,r = divmod(len(self),p);
    if r :
      raise ParameterError('desired dimensions not possible');
    if x < 0 :
      if q != 1 :
        raise ParameterError('desired dimensions not possible');
    else :
      dims[x] = q;
    return type(self)(dims,self.__v);

  def dot(self,other) :
    """Return the dot product of two bmatrices"""
    if islistlike(other) :
      other = type(self)((len(other),),other);
    elif isint(other) :
      other = type(self)(self.__dims, other);
    elif not isinstance(other,bmatrix) :
      raise TypeError('args must be vectors');
    if len(self) != len(other) :
      raise ParameterError('vectors must have same length');
    return parity(self.__v & other.__v); 

  def sum(self,*d) :
    """Return the sum of the array elements"""
    if d : raise NotImplementedError;
    return parity(self.__v);

  def product(self,*d) :
    """Return the product of the array elements"""
    if d : raise NotImplementedError;
    return 0+(self.__v==(1<<len(self))-1);

  def max(self,*d) :
    """Return the max of the array elements"""
    if d : raise NotImplementedError;
    return 0+(self.__v!=0);

  def min(self,*d) :
    """Return the min of the array elements"""
    if d : raise NotImplementedError;
    return self.product();

  def map(self,map,*d) :
    """Apply map to each element of the array"""
    # with no additional args, apply map to each element
    if not d :
      for i in xrange(len(self)) :
        self[i] = map(self[i]);
      return;
   # with one additional nonnegative integer arg, apply map to each vector
    #  along dimension d[0], and replace that vector with the result
    # with two ania, apply map to each 2D matrix along d[0] and d[1], ...
    raise NotImplementedError;

  mapply = map    # for backward compatibility

  def __neg__(self) :
    """Return a copy of the array"""
    return type(self)(self);

  def __invert__(self) :
    """Return a same-dimensioned array with each element complemented"""
    s = type(self)(self);
    s.__dict__[_v] = (1<<len(s))-1-s.__v;
    return s;

  def __iadd__(self, other) :
    """Add an array elementwise to this array, or,
if other is a scalar, add the scalar to each element of this array"""
    if isinstance(other,bmatrix) :
      if len(other) == 1 :
        if other.__v :
          self.__dict__[_v] ^= (1<<len(self))-1;
      elif other.__dims == self.__dims :
         self.__dict__[_v] ^= other.__v;
      elif len(self) == 1 :
        self.__dims[:] = other.__dims;
        self.__dict__[_v] = (1<<len(other)-1)^other.__v if self.__v else other.__v;
      else : raise ParameterError('matrices must have same dimensions');
    else :        # scalar
      if isint(other) :
        other &= 1;
      if other :
        self.__dict__[_v] ^= (1<<len(self))-1;
    return self;

  def __add__(self, other) :
    """Return the elementwise sum of two arrays, or, if other is a scalar,
return a copy of the first array with each element incremented by the scalar"""
    a = type(self)(self);
    return a.__iadd__(other);

  __radd__ = __add__;

  __isub__ = __iadd__;

  __sub__ = __add__;

  __rsub__ = __add__;

  __ixor__ = __iadd__

  __xor__ = __add__

  __rxor__ = __add__

  def __ior__(self,other) :
    """Or an array elementwise to this array, or,
if other is a scalar, or the scalar to each element of this array"""
    if isinstance(other,bmatrix) :
      if len(other) == 1 :
        if other.__v :
          self.__dict__[_v] = (1<<len(self))-1;
      elif other.__dims == self.__dims :
         self.__dict__[_v] |= other.__v;
      elif len(self) == 1 :
        self.__dims[:] = other.__dims;
        self.__dict__[_v] = (1<<len(other)-1) if self.__v else other.__v;
      else : raise ParameterError('matrices must have same dimensions');
    else :        # scalar
      if isint(other) :
        other &= 1;
      if other :
        self.__dict__[_v] = (1<<len(self))-1;
    return self;

  def __or__(self,other) :
    """Return the elementwise or of two arrays, or, if other is a scalar,
return a copy of the first array with each element or'd with the scalar"""
    a = type(self)(self);
    return a.__ior__(other);

  __ror__ = __or__


  def __iand__(self,other) :
    """And an array elementwise with this array, or,
if other is a scalar, and the scalar to each element of this array"""
    if isinstance(other,bmatrix) :
      if len(other) == 1 :
        if not other.__v :
          self.__dict__[_v] = 0;
      elif other.__dims == self.__dims :
         self.__dict__[_v] &= other.__v;
      elif len(self) == 1 :
        self.__dims[:] = other.__dims;
        self.__dict__[_v] = other.__v if self.__v else 0;
      else : raise ParameterError('matrices must have same dimensions');
    else :        # scalar
      if isint(other) :
        other &= 1;
      if not other :
        self.__dict__[_v] = 0;
    return self;

  def __and__(self,other) :
    """Return the elementwise and of two arrays, or, if other is a scalar,
return a copy of the first array with each element and'd with the scalar"""
    a = type(self)(self);
    return a.__iand__(other);

  __rand__ = __and__

  def __imul__(self,other) :
    """Update self to be the product of self and other as follows:
any * scalar :  scalar multiply
1D * 1D:  dot product (sum of the elementwise products)
2D * 2D:  matrix multiply
2D * 1D  or  1D * 2D:  treat vector as row or column as appropriate"""
    if isinstance(other,bmatrix) :
      if len(other) == 1 :           # other is scalar
        if not other.__v :
          self.__dict__[_v] = 0;
      elif len(self) == 1 :          # self is scalar
        self.__dims[:] = other.__dims;
        self.__dict__[_v] = other.__v if self.__v else 0;
      elif len(self.__dims) == 1 :       # self is 1D matrix
        if len(other.__dims) == 1 :        # 1D x 1D
          if len(self) != len(other) :
            raise ParameterError('vectors must have same length');
          self.__dims[:] = [];
          self.__dict__[_v] = parity(self.__v & other.__v);
        elif len(other.__dims) == 2 :      # 1D x 2D
          n = self.__dims[0];
          r,c = other.__dims;
          if n != r :
            raise ParameterError('inner dimensions must agree');
          v = self.__v;
          w = other.__v;
          x = 0;
          for k in reversed(xrange(c)) :
            x = (x<<1)|parity(v&(w>>k*n));
          self.__dims[:] = [c];
          self.__dict__[_v] = x;
        else : raise TypeError('only matrices can be multiplied');
      elif len(self.__dims) == 2 :       # self is 2D matrix
        rows,js = self.__dims;
        if len(other.__dims) <= 2 :        # 2D x 1D or 2D x 2D
          if js != other.__dims[0] :
            raise ParameterError('inner dimensions must agree');
          t = self.bT(rows,js,self.__v);
          v = other.__v;
          self.__dims[1] = cols = 1 if len(other.__dims) < 2 else other.__dims[1];
          w = 0;
          m = (1<<js)-1;
          for c in reversed(xrange(cols)) :      # col of result
            x = (v>>js*c)&m;
            for r in reversed(xrange(rows)) :    # row of result
              w = (w<<1)|parity(x&(t>>js*r));
          self.__dict__[_v] = w;
          if len(other.__dims) < 2 : del self.__dims[1];   # preserve vectorness
        else : raise TypeError('only matrices can be multiplied');
      else : raise TypeError('only matrices can be multiplied');
    elif islistlike(other) :
      return self.__imul__(matrix(len(other),other));
    elif not (other&1 if isint(other) else other) :    # matrix * scalar
      self.__dict__[_v] = 0;
    return self;

  def __mul__(self,other) :
    """Return the product of the two args, as for __imul__"""
    return type(self)(self).__imul__(other);

  def __rmul__(self,other) :    # can only be scalar*matrix or vector*matrix
    """Return the product of the two args, as for __imul__"""
    if islistlike(other) :
      return type(self)(len(other),other).__imul__(self);
    return type(self)(self.__dims,self.__v if (other&1 if isint(other) else other) else 0);

  def __itruediv__(self,b) :
    """Multiply self by b**-1"""
    return self.__imul__(b**-1);

  __idiv__ = __itruediv__;

  def __truediv__(self,b) :
    """Return the product self*b**-1"""
    return type(self)(self).__itruediv__(b);

  __div__ = __truediv__;

  def __rtruediv__(self,b) :
    """Return the product b*self**-1"""
    return b*self.inverse;

  __rdiv__ = __rtruediv__;

  def __ipow__(self,x) :
    """Raise a scalar to a power or a square matrix to an integer power"""
    # compute self**x; self must be square matrix and x must be integer
    # if x < 0, self must be invertible
    if len(self) == 1 :    # scalar
      self.__dict__[_v] = self.__v**x;
      return self;
    n = self.__dims[0];    # number of rows
    if len(self.__dims) != 2 or n != self.__dims[1] :
      raise TypeError('base must be square bmatrix') ;
    e = int(x);
    if e != x : raise TypeError('requires integer exponent');
    if e < 0 :
      m = self.inverse;
      e = -e;
    else :
      m = type(self)(self);
    v = 1;
    for i in xrange(n-1) :
      v = (v<<(n+1))|1;
    self.__dict__[_v] = v;
    while e :
      if e&1 : self *= m;
      e >>= 1;
      if not e : break;
      m *= m;
    return self;

  def __pow__(self,x) :
    """Return the exponentiation of a scalar to a power or a square bmatrix to an integer power"""
    return type(self)(self).__ipow__(x);

  # no rpow: can only work for real matrix exponents

  @staticmethod
  def Identity(n,m=1) :
    """Return an nxn identity bmatrix multiplied by the scalar m (either 0 or 1)"""
    if m not in (0,1) :
      raise ParameterError('multiplier must be 0 or 1');
    if m :
      v = 1;
      for i in xrange(n-1) :
        v = (v<<(n+1))|1;
    else :
      v = 0;
    return bmatrix((n,n),v);

  @staticmethod
  def circulant(row) :
    """Return a circulant bmatrix given its first row"""
    n = len(row);
    M = bmatrix(n,n);
    for r in range(n) :
      M[r,:r] = row[n-r:];
      M[r,r:] = row[:n-r];
    return M;

  @staticmethod
  def bT(rows,cols,v) :
    """Assuming v represents a bmatrix with the specified number of rows and columns,
  columnwise and little-endian bit-by-bit, return the representation of the transpose"""
    t = 0;
    for r in reversed(xrange(rows)) :
      for c in reversed(xrange(cols)) :
        t = (t<<1)|(v>>(c*rows+r))&1;
    return t;
