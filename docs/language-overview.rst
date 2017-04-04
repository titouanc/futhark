.. _language-overview:

Language Overview
=================

The Futhark programming language is a purely functional,
call-by-value, mostly first-order language that permits bulk
operations on arrays using *second-order array combinators* (SOACs).

The primary idea behind Futhark is to design a language that has
enough expressive power to conveniently express complex programs, yet
is also amenable to aggressive optimisation and parallelisation.  The
tension is that as the expressive power of a language grows, the
difficulty of efficient compilation rises likewise.  For example,
Futhark supports nested parallelism, despite the complexities of
efficiently mapping it to the flat parallelism supported by hardware,
as many algorithms are awkward to write with just flat parallelism.
On the other hand, we do not support non-regular arrays, as they
complicate size analysis a great deal.  The fact that Futhark is
purely functional is intended to give an optimising compiler more
leeway in rearranging the code and performing high-level
optimisations.  It is also the plan to eventually design a rigorous
cost model for Futhark, although this work has not yet been completed.

Lexical Syntax
--------------

The syntax of Futhark is derived from Haskell and Standard ML,
although somewhat less flexible.  Futhark is not whitespace-sensitive,
and indentation is only used for readability.  An identifier starts
with a lowercase letter, followed by any number of letters, digits,
apostrophes and underscores.  An identifier may also start with an
underscore, which is used to indicate that the name will not be used.
A structure identifier starts with an uppercase letter.  Numeric,
string and character literals use the same notation as Haskell (which
is very similar to C), including all escape characters.  Comments are
indicated with ``--`` and span to end of line.  Block comments are not
presently supported.

Simple Futhark
--------------

An Futhark program consists of a sequence of *function definitions*,
of the following form::

   let name params... : return_type = body

A function must declare both its return type and the types of all its
parameters.  All functions (except for inline anonymous functions; see
below) are defined globally.  Futhark does not use type inference.  As
a concrete example, here is the a parallel definition of the factorial
function in Futhark::

  let fact(n: i32): i32 =
    reduce (*) 1 (map (1+) (iota n))

Indentation has no syntactical significance in Futhark, but recommended for
readability.

The syntax for tuple types is a comma-separated list of types or
values enclosed in parentheses, so ``(i32, real)`` is a pair of an
integer and a floating-point number.  Single-element and empty tuples
are not permitted.  Array types are written as the element type
preceded by brackets, meaning that ``[]i32`` is a one-dimensional
array of integers, and ``[][][](i32, real)`` is a three-dimensional
array of tuples of integers and floats.  An array value is written as
a sequence of elements enclosed by brackets::

  [1, 2, 3]       -- Array of type []i32.
  [[1], [2], [3]] -- Array of type [][]i32.

All arrays must be *regular* (often termed *full*).  This means that,
for example, all rows of a two-dimensional array must have the same
number of elements::

  [[1, 2], [3]]      -- Compile-time error.
  [iota(1), iota(2)] -- A run-time error if reached.

The restriction to regular arrays simplifies compilation.

Arrays are indexed using the common row-major notation, e.g., ``a[i1,
i2, i3...]``.  An indexing is said to be *full* if the number of given
indices is equal to the dimensionality of the array.

A ``let``-expression can be used to refer to the result of a
subexpression::

  let z = x + y in ...

Recall that Futhark is eagerly evaluated, so the right-hand side of
the ``let`` is evaluated exactly once, at the time it is first
encountered.  The ``in`` keyword is optional when it precedes another
``let``.  This means that instead of writing::

  let a = 0 in
  let b = 1 in
  let c = 2 in
  a + b + c

we can write::

  let a = 0
  let b = 1
  let c = 2
  in a + b + c

The final ``in`` is still necessary.

Two-way ``if-then-else`` is the only branching construct in Futhark.
Pattern matching is supported in a limited way for taking apart
tuples, for example::

  let sumpair((x, y): (i32, i32)): i32 = x + y

We can also add the type ascription on the tuple components::

  let sumpair(x: i32, y: i32): i32 = x + y

Apart from pattern-matching, the components of a tuple can also be
accessed by using the tuple projection syntax: ``#i``, where ``i``
indicates the component to extract (0-indexed)::

  let sumpair(p: (i32, i32)): i32 = #0 p + #1 p

In most cases, pattern matching is better style.

Function calls are written as the function name with the arguments
juxtaposed.  All function calls must be fully saturated - currying is
only permitted in SOACs_.

Sequential Loops
~~~~~~~~~~~~~~~~

Futhark has a built-in syntax for expressing certain tail-recursive
functions.  Consider the following tail-recursive formulation of a
function for computing the Fibonacci numbers::

  let fib(n: i32): i32 = fibhelper(1,1,n)

  let fibhelper(x: i32, y: i32, n: i32): i32 =
    if n == 1 then x else fibhelper(y, x+y, n-1)

This is not valid Futhark, as Futhark does not presently allow
recursive functions.  Instead, we can write this using the ``loop``
construct::

  let fib(n: i32): i32 =
    loop ((x, y) = (1,1)) = for i < n do
                              (y, x+y)
    in x

The semantics of this is precisely as in the tail-recursive function
formulation.  In general, a loop::

  loop (pat = initial) = for i < bound do loopbody
  in body

Has the following the semantics:

1. Bind *pat* to the initial values given in *initial*.

2. While *i < bound*, evaluate *loopbody*, rebinding *pat* to be the
   value returned by the body.  At the end of each iteration, increment
   *i* by one.

3. Evaluate *body* with *pat* bound to its final value.

Semantically, a ``loop`` expression is completely equivalent to a
call to its corresponding tail-recursive function.

For example, denoting by ``t`` the type of ``x``, this loop::

  loop (x = a) =
    for i < n do
      g(x)
    in body

has the semantics of a call to this tail-recursive function::

  let f(i: i32, n: i32, x: t): t =
    if i >= n then x
       else f(i+1, n, g(x))

  let x = f(i, n, a)
  in body

The purpose of ``loop`` is partly to render some sequential
computations slightly more convenient, but primarily to express
certain very specific forms of recursive functions, specifically those
with a fixed iteration count.  This property is used for analysis and
optimisation by the Futhark compiler.

Apart from the ``i < n`` form, which loops from zero, Futhark also
supports the ``v <= i < n`` form which starts at ``v``.  We can also
invert the order of iteration by writing ``n > i`` or ``n > i >= v``,
which loops down from the upper bound to the lower.  Due to parser
limitations, most non-atomic expressions will have to be parenthesised
when used as the left-hand bound.

Apart from ``for``-loops, Futhark also supports ``while`` loops.
These do not provide as much information to the compiler, but can be
used for convergence loops, where the number of iterations cannot be
predicted in advance.  For example, the following program doubles a
given number until it exceeds a given threshold value::

  let main(x: i32, bound: i32): i32 =
    loop (x) = while x < bound do x * 2
    in x

In all respects other than termination criteria, ``while``-loops
behave identically to ``for``-loops.

For brevity, the initial value expression can be elided, in which case
an expression equivalent to the pattern is implied.  This is easier to
understand with an example.  The loop::

  let fib(n: i32): i32 =
    let x = 1
    let y = 1
    loop ((x, y) = (x, y)) = for i < n do (y, x+y)
    in x

can also be written::

  let fib(n: i32): i32 =
    let x = 1
    let y = 1
    loop ((x, y)) = for i < n do (y, x+y)
    in x

This can sometimes make imperative code look more natural.

Shape Declarations
~~~~~~~~~~~~~~~~~~

Optionally, the programmer may put *shape declarations* in the return
type and parameter types of a function declaration.  These can be used
to express invariants about the shapes of arrays that are accepted or
produced by the function, e.g::

  let f (a: [n]i32): [n]i32 =
    map (+1) a

The above declaration specifies a function that accepts an array
containing ``n`` elements and returns an array likewise containing
``n`` elements.  In general, shape declarations in parameters are
fresh names, whilst shape declarations in return types must refer to a
name of type ``i32`` in scope.  A shape declaration can also be an
integer constant (with no suffix).

The same name can be used in several dimensions, or even in several
parameters.  This can be used to give a natural type to a function for
computing dot products::

  let dotProduct(a: [n]i32, b: [n]i32): i32 =
    reduce (+) 0 (map (*) a b)

Or matrix multiplication::

  let matMult(x: [n][m]i32, y: [m][n]i32): [n][n]i32 =
    ...

The dimension names bound in a parameter shape declaration can be used
as ordinary variables inside the scope of the parameter.

Shape declarations serve two main purposes:

1. They document the shape assumptions of the function in an easily
   understandable form.

2. More importantly, they help the compiler understand the invariants
   of the program, which it may otherwise have trouble figuring out.

Note that adding shape declarations is never unsafe - the compiler
still inserts dynamic checks, so if an incorrect declaration is made,
the result will merely be an abrubt but controlled termination as it
collides with reality.  Shape declarations matter most when used for
the input parameters of the ``main`` function and for the return type
of functions used to ``map``.

In-Place Updates
~~~~~~~~~~~~~~~~

In an array programming language, we tend to use bulk operations for
most array manipulation.  However, sometimes it is useful to directly
replace some element.  In a pure language, we cannot permit free
mutation, but we can permit the creation of a duplicate array, where
some elements have been changed.  General modification of array
elements is done using the ``let-with`` construct.  In its most
general form, it looks as follows::

  let dest = src with [indexes] <- (value)
  in body

This evaluates ``body`` with ``dest`` bound to the value of ``src``,
except that the element(s) at the position given by ``indexes`` take
on the new value ``value``.  Due to parser limitations, the
parenthesis around ``value`` are not optional.  The given indexes need
not be complete, but in that case, ``value`` must be an array of the
proper size.  As an example, here's how we could replace the third row
of an ``n * 3`` array::

  let b = a with [2] <- ([1,2,3]) in b

As a convenience, whenever ``dest`` and ``src`` are the same, we can
write::

    let dest[indexes] = value in body

as a shortcut.  Note that this has no special semantic meaning, but is
simply a case of normal name shadowing.

For example, this loop implements the "imperative" version of matrix
multiplication of an ``m * o`` with an ``o * n`` matrix::

  let matmult(a: [m][o]f32,  b: [o][n]f32): [m][n]f32 =
    let res = replicate(m, replicate(n,0f32)) in
    loop (res) = for i < m do
        loop (res) = for j < n do
            loop (partsum = 0f32) = for k < o do
              partsum + a[i,k] * b[k,j]
            let res[i,j] = partsum
            in res
        in res
    in res

With the naive implementation based on copying the source array,
executing the ``let-with`` expression would require memory
proportional to the entire source array, rather than proportional to
the slice we are changing.  This is not ideal.  Therefore, the
``let-with`` construct has some unusual restrictions to permit
in-place modification of the ``src`` array, as described in
:ref:`uniqueness-types`.  Simply put, we track that ``src`` is never used
again.  The consequence is that we can guarantee that the execution of
a ``let-with`` expression does not involve any copying of the source
array in order to create the newly bound array, and therefore the time
required for the update is proportional to the section of the array we
are updating, not the entire array.  We can think of this as similar
to array modification in an imperative language.

SOACs
-----

The language presented in the previous section is in some sense
"sufficient", in that it is Turing-complete, and can express
imperative-style loops in a natural way with ``do`` and
``while``-loops.  However, Futhark is not intended to be used in this
way - bulk operations on arrays should be expressed via one of the
*second-order array combinators* (SOACs) shown below, as this
maximises the amount of parallelism that the compiler is able to take
advantage of.

.. productionlist::
   e: "map" `lambda` `e`
    : "filter" `lambda` `e`
    : "partition" "(" `lambda` "," ... `lambda` ")" `e`
    : "reduce" `lambda` `e` `e`
    : "scan" `lambda` `e` `e`

A lambda can be an anonymous function, the name of a function (with
optional curried arguments), or an operator (possibly with one operand
curried):

.. productionlist::
   lambda: "(" \ `param`... : `rettype` "->" `e` ")"
         : `fname`
         : "(" `fname` `e` ... `e` ")"
         : "(" `op` `e` ")"
         : "(" `e` `op` ")"
         : "(" `op` ")"

Parameter- and return type ascriptions are optional in anonymous
functions.  The semantics of the SOACs is identical to the
similarly-named higher-order functions found in many functional
languages.  For specifics, see :ref:`language-reference`.

The ``scan`` SOAC performs an inclusive prefix scan, and returns an
array of the same outer size as the original array.  The functions
given to ``reduce`` and ``scan`` must be binary associative operators,
and the value given as the initial value of the accumulator must be
the neutral element for the function.  These properties are not
checked by the Futhark compiler, and are the responsibility of the
programmer.

.. _uniqueness-types:

Uniqueness Types
----------------

While Futhark is uncompromisingly a pure functional language, it may
occasionally prove useful to express certain algorithms in an
imperative style.  Consider a function for computing the *n* first
Fibonacci numbers::

  let fib(n: i32): []i32 =
    -- Create "empty" array.
    let arr = iota(n) in
    -- Fill array with Fibonacci numbers.
    loop (arr) = for i < n-2 do
                   let arr[i+2] = arr[i] + arr[i+1]
                   in arr
    in arr

If the array ``arr`` is copied for each iteration of the loop, we
are going to put enormous pressure on memory, and spend a lot of time
moving around data, even though it is clear in this case that the
"old" value of ``arr`` will never be used again.  Precisely,
what should be an algorithm with complexity *O(n)* becomes *(n^2)*
due to copying the size *n* array (an *O(n)* operation) for each of
the *n* iterations of the loop.

To prevent this, we will want to update the array *in-place*,
that is, with a static guarantee that the operation will not require
any additional memory allocation, such as copying the entire array.  With an
in-place modification, a ``let-with`` can modify the array in
time proportional to the slice being updated (*O(1)* in the case of
the Fibonacci function), rather than time proportional to the size of
the final array, as would the case if we performed a full copy.  In order to
perform the update without violating referential transparency, we need
to know that no other references to the array exists, or at least that
such references will not be used on any execution path following the
in-place update.

In Futhark, this is done through a type system feature called
*uniqueness types*, similar to, although simpler, than the uniqueness
types of Clean.  Alongside a (relatively) simple aliasing analysis in
the type checker, this is sufficient to determine at compile time
whether an in-place modification is safe, and signal a compile time
error if ``let-with`` is used in way where safety cannot be
guaranteed.

The simplest way to introduce uniqueness types is through examples.
To that end, let us consider the following function definition::

  let modify(a: *[]i32, i: i32, x: i32): *[]i32 =
    let a[i] = a[i] + x in
    a

The function call ``modify(a,i,x)`` returns ``a``, but where the
element at index ``i`` has been increased by ``x``.  Note the
asterisks in the parameter declaration ``*[]i32 a``.  This means that
the function ``modify`` has been given "ownership" of the array ``a``,
meaning that the caller of ``modify`` will never reference array ``a`` after
the call.  As a consequence, ``modify`` can change the element at index
``i`` without first copying the array, i.e. ``modify`` is free to do
an in-place modification.  Furthermore, the return value of ``modify``
is also unique - this means that the result of the call to ``modify``
does not share elements with any other visible variables.

Let us consider a call to ``modify``, which might look as
follows::

  let b = modify(a, i, x) in
  ..

Under which circumstances is this call valid?  Two things must hold:

1. The type of ``a`` must be ``*[]i32``, of course.

2. Neither ``a`` or any variable that *aliases* ``a`` may be used on any
   execution path following the call to ``modify``.

In general, when a value is passed as a unique-typed argument in a
function call, we consider that value to be *consumed*, and neither it
nor any of its aliases can be used again.  Otherwise, we would break
the contract that gives the function liberty to manipulate the
argument however it wants.  Note that it is the type in the argument
declaration that must be unique - it is permissible to pass a
unique-typed variable as a non-unique argument (that is, a unique type
is a subtype of the corresponding nonunique type).

A variable *v* aliases *a* if they may share some elements,
i.e. overlap in memory.  As the most trivial case, after evaluating
the binding ``let b = a``, the variable ``b`` will alias
``a``.  As another example, if we extract a row from a
two-dimensional array, the row will alias its source::

  let b = a[0] in
  ... -- b is aliased to a (assuming a is not one-dimensional)

In :ref:`futhark-sharing` below, we will cover sharing and sharing
analysis in greater detail.

Let us consider the definition of a function returning a unique array::

  let f(a: []i32): *[]i32 = body

Note that the argument, ``a``, is non-unique, and hence we cannot
modify it.  There is another restriction as well: ``a`` must not be
aliased to our return value, as the uniqueness contract requires us to
ensure that there are no other references to the unique return value.
This requirement would be violated if we permitted the return value in
a unique-returning function to alias its non-unique parameters.

To summarise: *values are consumed by being the source in a
``let-with``, or by being passed as a unique parameter in a function
call*.  We can crystallise valid usage in the form of three principal
rules:

  **Uniqueness Rule 1**

    When a value is passed in the place of a unique parameter in a
    function call, or used as the source in a ``let-with`` expression,
    neither that value, nor any value that aliases it, may be used on
    any execution path following the function call.  An example
    violation::

      let b = a
      let b[i] = 2 in
      f(b,a) -- Error: a used after being source in a let-with


  **Uniqueness Rule 2**

    If a function definition is declared to return a unique value, the
    return value (that is, the result of the body of the function)
    must not share memory with any non-unique arguments to the
    function.  As a consequence, at the time of execution, the result
    of a call to the function is the only reference to that value.  An
    example violation::

      let broken(a: [][]i32, i: i32): *[]i32 =
        a[i] -- Return value aliased with 'a'.

  **Uniqueness Rule 3**

    If a function call yields a unique return value, the caller has
    exclusive access to that value.  At *the point the call returns*,
    the return value may not share memory with any variable used in
    any execution path following the function call.  This rule is
    particularly subtle, but can be considered a rephrasing of
    Uniqueness Rule 2 from the "calling side".

It is worth emphasising that everything in this chapter is employed as
part of a static analysis.  *All* violations of the uniqueness rules
will be discovered at compile time during type-checking, thus leaving
the code generator and runtime system at liberty to exploit them for
low-level optimisation.

.. _futhark-sharing:

Sharing Analysis
~~~~~~~~~~~~~~~~

Whenever the memory regions for two values overlap, we say that they
are *aliased*, or that *sharing* is present.  As an example, if you
have a two-dimensional array ``a`` and extract its first row as the
one-dimensional array ``b``, we say that ``a`` and ``b`` are aliased.
While the Futhark compiler may do a deep copy if it wishes, it is not
required, and this operation thus holds the potential for sharing
memory.  Sharing analysis is necessarily conservative, and merely
imposes an upper bound on the amount of sharing happening at runtime.
The sharing analysis in Futhark has been carefully designed to make
the bound as tight as possible, but still easily computable.

In Futhark, the only values that can have any sharing are arrays -
everything else is considered "primitive".  Tuples are special, in
that they are not considered to have any identity beyond their
elements.  Therefore, when we store sharing information for a
tuple-typed expression, we do it for each of its element types, rather
than the tuple value as a whole.

Most operations produce arrays without any aliases.  You can think of
these as producing fresh arrays.  The exceptions are ``split``,
``reshape``, ``transpose``, ``rearrange``, ``zip`` and ``unzip``, as
well as function calls and ``if`` expressions (depending on types).
You can use ``copy`` to "break" sharing by forcing the argument to be
manifested freshly in memory.
