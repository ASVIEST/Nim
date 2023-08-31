{.experimental: "inferGenericTypes".}

block inferTypesWithUnderscore:
  type T[A, B] = object
    x: A
    y: B
  
  let x: T[int, float] = T[_, float](x: int.default, y: float.default)
  doAssert x.x is int
  doAssert x.y is float

  let y: T[int, _] = T[_, float](x: int.default, y: float.default)
  doAssert y.x is int
  doAssert y.y is float
  
  let z: T[_, _] = T[int, float](x: int.default, y: float.default)
  doAssert z.x is int
  doAssert z.y is float
  
  let w: T[int, float] = T[_, _](x: int.default, y: float.default)
  doAssert w.x is int
  doAssert w.y is float

  let f: T[int, float] = T(x: int.default, y: float.default)
  doAssert f.x is int
  doAssert f.y is float

block:
  type
    A[T] = object
      x: T

    B[T] = object
      x: T

  proc giveValue[T]: T = discard


  let foo: (A[int], B[int]) = (A(x: 42), B(x: 42))

  doAssert foo[0] is A[int]
  doAssert foo[0].x == 42

  doAssert foo[1] is B[int]
  doAssert foo[1].x == 42

  let bar: A[B[int]] = A(x: B(x: 42))
  
  doAssert bar is A[B[int]]
  doAssert bar.x.x == 42

  let baz: A[B[int]] = A(x: B(x: giveValue()))

  doAssert baz is A[B[int]]
  doAssert baz.x.x == 0
