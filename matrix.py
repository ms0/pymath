#matlab-style multidimensional arrays
#matrix elements can be any sort of interoperable numbers
#for example, matrices over a finite field can use elements from ffield.py

from __future__ import division

import sys
import types
import math
from fractions import gcd as gcd

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
  for i in range(len(v1)) :
    s += v1[i]*v2[i];
  return s;

def matmul(p,q,r,v1,v2) :
  """Multiply pxq array of elements v1 by qxr array of elements v2, result is pxr"""
  v = [0]*(p*r);
  for i in range(p) :
    for k in range(r) :
      v[i+k*p] = dot(v1[i::p],v2[k*q:(k+1)*q]);
  return v;

def listr(v) :    # output string for list, using str rather than repr
  return '[ '+', '.join(map(str,v))+' ]';

class matrix() :    # multidimensional array
  """Multidimensional array
2-D: matrix(nrows,ncolumns)
1-D (so nrows only), can be considered a column vector or a row vector

 An array is stored as a list v, so for dims = [A,B,C,D,...],
 M[a,b,c,d,...] = v[a+A*(b+B*(c+C*(d+D*...)))]
 so consecutive elements are down rows, then over columns, then ...

Instance variables:
  dims: a tuple giving the dimensions of the array
  tr or trace: the trace of the [square] matrix
  squeeze: an array with the same elements but all length-1 dimensions removed
  T or transpose: the transpose of the matrix [of dimension <= 2]
  det or determinant: the determinant of the [square] matrix
  inverse: the inverse of the [square] matrix
Methods:
  __init__, __repr__, __str__, __getitem__, __getattr__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
  __neg__, __iadd__, __add__, __radd__, __isub__, __sub__, __rsub__,
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
      for i in range(n) :
        if n > 1 : s.append(str(tuple(c)) + ' :');
        m = self.__v[i*rc:(i+1)*rc];
        for r in range(self.__dims[0]) :
          s.append(listr(m[r::self.__dims[0]]));
        for j in range(len(c)) :
          c[j] = (c[j]+1) % d[j];
          if c[j] : break;
    return '\n'.join(s);

  #### comparison operators ####

  def __lt__(self,other) :
    """Return True iff each element of first array < corresponding element of the other"""
    if len(self.__v) == 1 :    #scalar
      return self.__v[0] < other;
    if not isinstance(other,matrix) or self.__dims != other.__dims :
      raise TypeError('only matrices of identical dimensions can be compared');
    for i in range(len(self.__v)) :
      if not self.__v[i] < other.__v[i] : return False;
    return True;

  def __le__(self,other) :
    """Return True iff each element of first array <= corresponding element of the other"""
    if len(self.__v) == 1 :    #scalar
      return self.__v[0] <= other;
    if not isinstance(other,matrix) or self.__dims != other.__dims :
      raise TypeError('only matrices of identical dimensions can be compared');
    for i in range(len(self.__v)) :
      if not self.__v[i] <= other.__v[i] : return False;
    return True;

  def __eq__(self,other) :
    """Return True iff each element of first array == corresponding element of the other"""
    if len(self.__v) == 1 :    #scalar
      return self.__v[0] == other;
    else :
      return isinstance(other,matrix) and self.__dims == other.__dims and \
             self.__v == other.__v;

  def __ne__(self,other) :
    """Return False iff each element of first array == corresponding element of the other"""
    return not self == other;

  def __ge__(self,other) :
    """Return True iff each element of first array >= corresponding element of the other"""
    if len(self.__v) == 1 :    # scalar
      return self.__v[0] >= other;
    if not isinstance(other,matrix) or self.__dims != other.__dims :
      raise TypeError('only matrices of identical dimensions can be compared');
    for i in range(len(self.__v)) :
      if not self.__v[i] >= other.__v[i] : return False;
    return True;

  def __gt__(self,other) :    
    """Return True iff each element of first array > corresponding element of the other"""
    if len(self.__v) == 1 :    # scalar
      return self.__v[0] > other;
    if not isinstance(other,matrix) or self.__dims != other.__dims :
      raise TypeError('only matrices of identical dimensions can be compared');
    for i in range(len(self.__v)) :
      if not self.__v[i] > other.__v[i] : return False;
    return True;


  def __neg__(self) :
    """Return the additive inverse of the array"""
    s = matrix(self);
    for i in range(len(s.__v)) :
      s.__v[i] = -s.__v[i];
    return s;


  def __iadd__(self, other) :
    """Add an array elementwise to this array, or,
if other is a scalar, add the scalar to each element of this array"""
    if isinstance(other,matrix) :
      if len(other.__v) == 1 :
        for i in range(len(self.__v)) :
          self.__v[i] += other.__v[0];
      elif other.__dims == self.__dims :
        for i in range(len(self.__v)) :
          self.__v[i] += other.__v[i];
      elif len(self.__v) == 1 :
        self.__dims[:] = other.__dims;
        self.__v[:],other = other.__v,self.__v[0];
        for i in range(len(self.__v)) :
          self.__v[i] += other;
      else : raise ParameterError('matrices must have same dimensions');
    else :        # scalar
      for i in range(len(self.__v)) :
        self.__v[i] += other;
    return self;

  def __add__(self, other) :
    """Return the elementwise sum of two arrays, or, if other is a scalar,
return a copy of the first array with each element incremented by the scalar"""
    a = matrix(self);
    return a.__iadd__(other);

  __radd__ = __add__;


  def __isub__(self, other) :
    """Subtract an array elementwise from this array, or,
if other is a scalar, subtract the scalar from each element of this array"""
    if isinstance(other,matrix) :
      if len(other.__v) == 1 :
        for i in range(len(self.__v)) :
          self.__v[i] -= other.__v[0];
      elif other.__dims == self.__dims :
        for i in range(len(self.__v)) :
          self.__v[i] -= other.__v[i];
      else : raise ParameterError('matrices must have same dimensions');
    else :                # scalar
      for i in range(len(self.__v)) :
        self.__v[i] -= other;

    return self;

  def __sub__(self, other) :
    """Return the elementwise difference of two arrays, or, if other is a scalar,
return a copy of the first array with each element decremented by the scalar"""
    a = matrix(self);
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
        for i in range(len(self.__v)) :
          self.__v[i] *= other.__v[0];   # assume a *= b means a = a*b
      elif len(self.__v) == 1 :          # self is scalar
        c = self.__v[0];
        self.__v[:] = other.__v;
        for i in range(len(self.__v)) :
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
      return self.__imul__(matrix(len(other),other));
    else :    # matrix * scalar
      for i in range(len(self.__v)) :
        self.__v[i] *= other;
    return self;

  def __mul__(self,other) :
    """Return the product of the two args, as for __imul__"""
    return matrix(self).__imul__(other);

  def __rmul__(self,other) :    # can only be scalar*matrix or vector*matrix
    """Return the product of the two args, as for __imul__"""
    if islistlike(other) :
      return matrix(len(other),other).__imul__(self);
    b = matrix(self);
    for i in range(len(b.__v)) :
      b.__v[i] = other*b.__v[i];
    return b;

  def __itruediv__(self,b) :
    """Multiply self by b**-1"""
    return self.__imul__(b**-1);

  __idiv__ = __itruediv__;

  def __truediv__(self,b) :
    """Return the product self*b**-1"""
    return matrix(self).__itruediv__(b);

  __div__ = __truediv__;

  def __rtruediv__(self,b) :
    """Return the product b*self**-1"""
    return b*self.inverse;

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
      m = matrix(self);
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
    return matrix(self).__ipow__(x);

  def __rpow__(self,b) :
    """Return a positive real number b to a scalar or square matrix power"""
    # base ** matrix
    if not isreal(b) or not b > 0 :
      return TypeError('base must be positive real');
    if len(self.__v) == 1 :
      return matrix(self.__dims,b**self.__v[0]);
    n = self.__dims[0];
    if len(self.__dims) != 2 or n != self.__dims[1] :
      return TypeError('exponent must be square matrix');
    n2 = n*n;
    P = math.log(b)*self;
    S = Identity(n);
    M = Identity(n);
    for x in range(1,10001) :
      M *= P;
      M /= x;
      v = S.__v[:];
      S += M;
      if v == S.__v : break;
    return S;

  def __abs__(self) :
    """Return the square root of the sum of the squares of the array elements"""
    s = 0;
    for x in self.__v :
      s += x*x;
    return math.sqrt(s);

  def __len__(self) :
    """Return the number of elements in the array"""
    return len(self.__v);

# we have to be able to do multi-dimensional indexing
# for slices, key is type slice, with attributes start stop step

  def __getitem__(self,key) :
    """Return an item or slice of the array;
if the specified slice or index is singly dimensioned, but the array isn't,
treat the array is a list of its elements in storage order"""
    if not isinstance(key,tuple) :
      v = self.__v[key];    # linear indexing always allowed
      if isint(key) or not v or len(self.__dims) > 1 :
        # if key is just a linear index, or
        #    key is a slice with no elements, or
        #    have multiple dimensions, then return the element or element list
        return v;
      # return the submatrix...
      return matrix([len(v)] if self.__dims else [] ,v);
    if len(key) != len(self.__dims) :
      raise ParameterError('length of index list must be number of dimensions');
    key = list(key);    # so can modify it
    # figure out dims of result, which depends on slices
    dims = [];
    single = True;
    for i in range(len(self.__dims)) :
      if isinstance(key[i],slice) :
        key[i] = key[i].indices(self.__dims[i]);
        dim = (key[i][1]-key[i][0])//key[i][2];
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
      for i in reversed(range(len(key))) :
        s = s*self.__dims[i] + key[i][0];
      return self.__v[s];
    # must return a submatrix...
    v = [];
    x = [0]*len(dims);
    while True :
      s = 0;
      for i in reversed(range(len(key))) :
        if len(key[i]) == 1 :
          s = s*self.__dims[i] + key[i][0];
        else :
          s = s*self.__dims[i] + range(*key[i])[x[i]];
      v.append(self.__v[s]);
      for i in range(len(dims)) :
        x[i] = (x[i]+1)%dims[i];
        if x[i] : break;
      else : break;
    for i in reversed(range(len(dims))) :
      if len(key[i]) == 1 : del dims[i];
    return matrix(dims,v);


  def __setitem__(self,key,value) :
    """Set an item or slice of the array, interpreting key as for __getitem__;
when setting a slice, value must have length matching size of slice"""
    if not isinstance(key,tuple) :
      if isinstance(key,slice) :
        k = key.indices(len(self.__v));
        dim = (k[1]-k[0])//k[2];
        if isreal(value) :
          for i in range(*k) : self.__v[i] = value;
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
    for i in range(len(self.__dims)) :
      if isinstance(key[i],slice) :
        key[i] = key[i].indices(self.__dims[i]);
        dim = (key[i][1]-key[i][0])//key[i][2];
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
      for i in reversed(range(len(key))) :
        s = s*self.__dims[i] + key[i][0];
      self.__v[s] = value;
      return;
    # must set a submatrix...
    pdims = product(dims);
    if not isreal(value) and pdims != len(value) :
      raise TypeError('value must have same length as slice');
    x = [0]*len(dims);
    for j in range(pdims) :
      s = 0;
      for i in reversed(range(len(key))) :
        if len(key[i]) == 1 :
          s = s*self.__dims[i] + key[i][0];
        else :
          s = s*self.__dims[i] + range(*key[i])[x[i]];
      self.__v[s] = value if isreal(value) else value[j];
      for i in range(len(dims)) :
        x[i] = (x[i]+1)%dims[i];
        if x[i] : break;
      else : break;
    for i in reversed(range(len(dims))) :
      if len(key[i]) == 1 : del dims[i];
    if isinstance(value,matrix) and dims != value.__dims :
      raise UserWarning('value and slice dimensions differ');
    return;

  def __getattr__(self,name) :
    """Return the specified attribute:
dims, tr(ace), T or transpose, det(erminant), or inverse"""

    # in order of how hard they are to create :
    
    # dims #

    if name == 'dims' :
      return tuple(self.__dims);

    # trace #

    if name == 'tr' or name == 'trace' :
      if len(self.__v) == 1 :
        return self.__v[0];
      n = self.__dims[0];
      if len(self.__dims) != 2 or n != self.__dims[1] :
        raise TypeError('requires square matrix') ;
      return sum(self.__v[0::(n+1)]);

    # squeeze #

    if name == 'squeeze' :
      # remove any dims of length 1
      s = matrix(self);
      for i in reversed(range(len(s.__dims))) :
        if s.__dims[i] == 1 : del s.__dims[i];
      return s;

    # transpose #

    if name == 'T' or name == 'transpose' :
      # if 2D, return transposed matrix
      # if 1D, return self
      # else, raise exception
      s = matrix(self);
      if len(s.__dims) == 2 :
        s.__dims[:] = self.__dims[1],self.__dims[0];
        for c in range(s.__dims[1]) :    # column of the result
          # copy a row to a column:
          s.__v[s.__dims[0]*c:s.__dims[0]*(c+1)] = self.__v[c::self.__dims[0]];
        return s;
      if len(s.__dims) == 1 :
        return s;
      raise AttributeError('transpose not defined for >=3D matrices');

    # determinant #

    if name == 'det' or name == 'determinant' :
      if len(self.__v) == 1 :
        return self.__v[0];
      n = self.__dims[0];
      if len(self.__dims) != 2 or n != self.__dims[1] :
        raise TypeError('determinant requires square matrix') ;
      integral = 1;
      v = self.__v[:];
      for x in v :
        if not isint(x) :
          integral = 0;
          break;
      if integral :
        d = 1;    # numerator
        dd = 1;   # denominator
        rows = list(range(n));
        for c in range(n-1) :    # for each column
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
            for cc in range(c+1,n) :
              v[r+n*cc] = ma*v[r+n*cc] - mx*v[pr+n*cc];
        return d*v[rows[0]+n*(n-1)]//dd;
      d = 1;
      rows = list(range(n));
      for c in range(n-1) :    # for each column
        x = 0;
        for r in rows :    # find pivot row (largest pivot element)
          a = abs(v[r+n*c]);
          if a > x :
            x = a;
            pr = r;
        if not x : return 0;
        x = v[pr+n*c];
        d *= x;
        for pc in range(c+1,n) :
          v[pr+n*pc] /= x;
        rx = rows.index(pr);
        if rx & 1 :
          d = -d;
        del rows[rx];
        for r in rows :
          a = v[r+n*c];
          for cc in range(c+1,n) :
            v[r+n*cc] -= a*v[pr+n*cc];
      return d*v[rows[0]+n*(n-1)];

    # inverse #

    if name == 'inverse' :
      if len(self.__v) == 1 :
        s = matrix(self);
        s.__v[0] = 1/s.__v[0];
        return s;
      n = self.__dims[0];
      if len(self.__dims) != 2 or n != self.__dims[1] :
        raise AttributeError('inverse requires square matrix') ;
      n2 = n*n;
      v = [0]*(n2);
      v[0::(n+1)] = (1,)*n;
      v += self.__v;
      for c in range(n) :
        x = 0;
        for r in range(c,n) :
          a = abs(v[n2+r+n*c]);
          if a > x :
            x = a;
            pr = r;
        if not x : raise ZeroDivisionError('matrix not invertible');
        if pr != c : v[c::n],v[pr::n] = v[pr::n],v[c::n];
        x = v[n2+c*(n+1)];
        if x != 1 :
          for cc in range(2*n) : v[c+n*cc] /= x;
        for r in range(c+1,n) :
          x = v[n2+r+n*c];
          for cc in range(2*n) :
            v[r+n*cc] -= x*v[c+n*cc];
      for c in reversed(range(1,n)) :
        for r in range(0,c) :
          x = v[n2+r+n*c];
          for cc in range(n) :
            v[r+n*cc] -= x*v[c+n*cc];
      return matrix(n,n,v[0:n*n]);

    raise AttributeError('matrix object has no attribute '+name);

  def __setattr__(self,name,value) :
    raise AttributeError('no matrix attributes can be set');

  def reshape(self,*dims) :
    """Return a new array with the same elements but different dimensions,
one dimension may be left unspecified (0 or None) and will be filled in,
the product of the new dimensions must equal the product of the old dimensions"""
    if len(dims) == 1 and islistlike(dims[0]) : dims = dims[0];
    for d in dims :
      if not isint(d) or d < 0 :
        raise TypeError('dimensions must be positive integers');
    x = -1;
    for i in range(len(dims)) :
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
    return matrix(dims,self.__v);

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

  def mapply(self,map,*d) :
    """Apply map to each element of the array"""
    # with no additional args, apply map to each element
    if not d :
      for i in range(len(self.__v)) :
        self.__v[i] = map(self.__v[i]);
      return;
   # with one additional nonnegative integer arg, apply map to each vector
    #  along dimension d[0], and replace that vector with the result
    # with two ania, apply map to each 2D matrix along d[0] and d[1], ...
    raise NotImplementedError;

def Identity(n,m=1) :
  """Return an nxn identity matrix multiplied by the scalar m"""
  v = [m*0]*(n*n);    # coerce 0 to same type as m
  v[0::(n+1)] = (m,)*n;
  I = matrix(n,n,v);
  return I;

def mapplied(m,map,*d) :
  """Return a copy of m with map applied to each element"""
  m = matrix(m);
  m.mapply(map,*d);
  return m;
