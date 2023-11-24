module main

// --------------------------------------------------------
//  Nondeterminism
// --------------------------------------------------------

effect nd
  ctl mplus() : bool
  ctl mzero() : a

fun hND(action)
  handle action
    return(x)  [x]
    ctl mplus() resume(True) ++ resume(False)
    ctl mzero() []

// --------------------------------------------------------
//  State
// --------------------------------------------------------

effect state<s>
  ctl get() : s
  ctl put( x : s ) : ()

fun hState(action)
  handle action
    return(x)  fn(s) (x, s)
    ctl get()  fn(s) resume(s)(s)
    ctl put(x) fn(s) resume(())(x)

// --------------------------------------------------------
//  Modify
// --------------------------------------------------------

effect modify<s, r>
  ctl mget() : s
  ctl update( x : r ) : ()
  ctl restore( x : r ) : ()

fun hModify(plus, minus, action)
  handle action
    return(x)  fn(s) (x, s)
    ctl mget()     fn(s) resume(s)(s)
    ctl update(r)  fn(s) resume(())(plus(s, r))
    ctl restore(r) fn(s) resume(())(minus(s, r))

// --------------------------------------------------------
//  Combine nondeterminism and state
// --------------------------------------------------------

pub fun hLocal(action: () -> <nd,state<a>|e> b, init: a) : e list<b>
  hND{ hState(action)(init) }.map(fst)

pub fun hGlobal(action: () -> <nd,state<a>|e> b, init: a) : e list<b>
  hState{ hND(action) }(init).fst

pub fun local2global(action: () -> <nd,state<a>,state<a>|e> b) : <nd,state<a>|e> b
  handle action
    ctl get()
      resume(get())
    ctl put(x)
      val s = get()
      if mplus() then put(x)
      else
        put(s)
        mzero()
      resume(())

// --------------------------------------------------------
//  Combine nondeterminism and modify
// --------------------------------------------------------

pub fun hLocalM(plus: (a, r) -> a, minus: (a, r) -> a, action: () -> <nd,modify<a,r>|e> b, init: a) : e list<b>
  hND{ hModify(plus, minus, action)(init) }.map(fst)

pub fun hGlobal(plus: (a, r) -> a, minus: (a, r) -> a, action: () -> <nd,modify<a,r>|e> b, init: a) : e list<b>
  hModify(plus, minus, { hND(action) })(init).fst

pub fun local2globalM(action: () -> <nd,modify<a,r>,modify<a,r>|e> b) : <nd,modify<a,r>|e> b
  handle action
    ctl mget()
      resume(mget())
    ctl update(r)
      if mplus() then update(r)
      else
        restore(r)
        mzero()
      resume(())
    ctl restore(r)
      resume(restore(r)) // this should never happen


// --------------------------------------------------------
//  N-queens
// --------------------------------------------------------
pub fun queens(n: int) : <div, nd, state<(int, list<int>)>> list<int>
  fun loop()
    val (c, sol) = get()
    if c >= n then return sol
    else
      val r = chooseList (list (1, n))
      guard (safe(r, 1, sol))
      val s = get()
      put(plus(s, r))
      loop()
  loop()

pub fun queensM(n: int) : <div, nd, modify<(int, list<int>), int>> list<int>
  fun loop()
    val (c, sol) = mget()
    if c >= n then return sol
    else
      val r = chooseList (list (1, n))
      guard (safe(r, 1, sol))
      update(r)
      loop()
  loop()

fun chooseList(xs: list<a>) : <nd> a
  match xs
    [] -> mzero()
    Cons(x,xs) -> if mplus() then x else chooseList(xs)

fun guard(b: bool): <nd> ()
  if b then return () else mzero()

fun safe(q: int, n: int, qs: list<int>): bool
  match qs
    [] -> True
    Cons(q1,qs) -> q != q1 && q!= q1 + n && q != q1 - n && safe(q, n+1, qs)

fun plus((c, sol): (int, list<int>), r: int): (int, list<int>)
  (c + 1, Cons(r, sol))

fun minus((c, sol): (int, list<int>), r: int): (int, list<int>)
  (c - 1, tail(sol))


// --------------------------------------------------------

pub fun main(n)
  print("hLocal: ")
  hLocal({queens(n)}, (0, [])).showll.println
  print("hGlobal: ")
  hGlobal({local2global{queens(n)}}, (0, [])).showll.println
  print("hLocalM: ")
  hLocalM(plus, minus, {queensM(n)}, (0, [])).showll.println
  print("hGlobalM: ")
  hGlobal(plus, minus, {local2globalM{queensM(n)}}, (0, [])).showll.println

fun showll( xs : list<list<int>> ) : string
  xs.show-list fn(x)
    x.show-list(show)