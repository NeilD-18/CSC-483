//Author: Neil Daterao

//============
// Problem 1.1
//============

/**
Notes:
Simple postcondition, just follow instructions. Also copy and pasted implementation, 
wasn't sure if needed or not
 */
method MinSum(x: int, y: int) returns (s: int, m: int)
    ensures s == x + y
    ensures m == if x <= y then x else y
{
    s := x + y;
    if x < y { m := x; } else { m := y; }
}
  
//============
// Problem 1.2
//============

/**
Notes
Guarantee that the minimum (m) is not greater than the sum (s). 
Solve by ensuring both x and y are positive. Why?
For example, if x = –5 and y = –3, then m would be –5 (since –5 < –3) and s would be –8, and –5 is not less than or equal to –8.
*/

method MinSum2(x: int, y: int) returns (s: int, m: int)
  requires x >= 0
  requires y >= 0
  ensures m <= s
{
  s := x + y;
  if x < y { m := x; } else { m := y; }
}


//============
// Problem 1.3
//============
/**
 Notes:
 This is absolute value! Always returning y as the magnitude of x.
 
 */
method M1(x: int) returns (y: int)
  ensures y >= 0
  ensures y == if x >= 0 then x else -x
{
  if x > 0 { y := x; } 
  else if x == 0 { y := 0; } else { y := -x; }
}

method M2(x: int) returns (y1: int, y2: int, y3: int)
  ensures y1 >= 0
  ensures y2 == y1
  ensures y3 == y1
  ensures y1 == x || -y1 == x
  ensures x == -3 ==> y1 == 3
{
   y1 := M1(x);
   y2 := M1(y1);
   y3 := M1(-x);
}


//============
// Problem 1.4
//============

/**
 Notes:

 Since we know what f(x) does, want to ensure m(x) has same functionality 
 */
function f(x:int): int 
{
  4 * x
}

method m(x: int) returns (y: int) 
  ensures y == 4 * x
{
  y := x + x;
  y := y + y;
}

method top(x: int) {
  var y := m(x);
  assert y == f(x);
}


//============
// Problem 1.5
//============
/**
Notes:
"with b at least as long as a" easy to see the pre-condition
"if and only if every element of a, if any, is equal to the corresponding element
of b." easy to see post-condition

Invariant #1: 0 <= i <= a.Length ensures the loop index stays within the valid bounds of array a.
Invariant #2: r <==> (forall j :: 0 <= j < i ==> a[j] == b[j]) guarantees that r is true iff the first i elements of a equal the corresponding elements of b.
Decreases Clause: a.Length - i acts as a countdown, ensures termination
*/
method isPrefix(a: array<int>, b: array<int>) returns (r: bool)
  requires b.Length >= a.Length
  ensures r <==> (forall i :: 0 <= i < a.Length ==> a[i] == b[i])

{
  var i := 0 ;
  r := true ; // if a is empty, it is trivially a prefix of b
  
    
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant r <==> (forall j :: 0 <= j < i ==> a[j] == b[j])
    decreases a.Length - i
  {
    r := r && (a[i] == b[i]);
    i := i + 1 ;
  }
 }


//===========
// Problem 2
//===========

/**
Precondition: n > 0 guarantees that the input is a positive integer.
Postcondition: ensures pow2(l) <= n < pow2(l + 1) specifies that the returned l is the largest natural number s.t 2^l is <= to n.
Invariant #1: 0 <= currLog ensures that the candidate logarithm remains non-negative.
Invariant #2: pow2(currLog) <= n guarantees that the current candidate currLog is valid. i.e 2^(currLog) does not exceed n.
Decreases Clause: n - pow2(currLog) acts as a countdown, ensuring the loop terminates as the gap between n and 2^(currLog) gets smaller with each iteration.
Iterative Process: The loop increments currLog until 2^(currLog + 1) exceeds n, at which point currLog is exactly the integer binary logarithm of n.
*/

function pow2(k: nat) : nat
{
  if k == 0 then 1 else 2 * pow2(k - 1)
}

method IntLog(n: nat) returns (l: nat)
  requires n > 0
  ensures pow2(l) <= n < pow2(l + 1)
{
  var currLog: nat := 0;
  while pow2(currLog + 1) <= n
    invariant 0 <= currLog
    invariant pow2(currLog) <= n
    decreases n - pow2(currLog)
  {
    currLog := currLog + 1;
  }
  l := currLog;
}


//===========
// Problem 3
//===========
/**
Notes:

Predicate sorted: (satisfying the sorted problem)
Asserts that for any indices i and j with 0 <= i < j < a.Length, the element a[i] is <= a[j], which means the array is sorted in non-decreasing order.

Outer Loop Invariants:

Invariant 1: 0 <= i <= a.Length ensures that the loop index i stays within the valid bounds of the array.
Invariant 2: forall k, l :: 0 <= k < l < i ==> a[k] <= a[l] guarantees that the subarray a[0..i) is sorted.
Invariant 3: forall k, l :: 0 <= k < i <= l < a.Length ==> a[k] <= a[l] ensures that every element in the sorted prefix (a[0..i)) is <= every element in the unsorted suffix (a[i..a.Length)).
Decreases Clause: a.Length - i acts as a countdown to guarantee termination of the outer loop.

Inner Loop Invariants:

Invariant 1: i + 1 <= j <= a.Length ensures that the inner loop index j is always within the valid range for the unsorted subarray.
Invariant 2: i <= mindex < a.Length ensures that mindex is a valid index within the unsorted portion.
Invariant 3: forall k :: i <= k < j ==> a[mindex] <= a[k] guarantees that mindex holds the index of the smallest element found so far in the subarray from i to j-1.
Decreases Clause: a.Length - j ensures that the inner loop terminates by counting down the remaining elements to be checked.


*/

predicate sorted(a: array<int>)
  reads a
  {
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  }

method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted(a)
{
  var i := 0;
  //Outer Loop
  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant (forall k, l :: 0 <= k < l < i ==> a[k] <= a[l])
    invariant (forall k, l :: 0 <= k < i <= l < a.Length ==> a[k] <= a[l])
    decreases a.Length - i
  {
    //Selects min element from i to end of array
    var mindex := i;
    var j := i + 1;
    
    
    //Inner loop
    while (j < a.Length)
      invariant i + 1 <= j <= a.Length
      invariant i <= mindex < a.Length
      invariant (forall k :: i <= k < j ==> a[mindex] <= a[k])
      decreases a.Length - j
    {
      if (a[j] < a[mindex]) {
        mindex := j;
      }
      j := j + 1;
    }
    //Swap min element with i
    a[i], a[mindex] := a[mindex], a[i];
    i := i + 1;
  }
}