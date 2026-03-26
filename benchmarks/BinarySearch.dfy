predicate sorted(a: array<int>, l: int, u: int)
{
	forall j, k :: 0 <= l <= j <= k <= u < a.Length ==> a[j] <= a[k]
}

predicate partitioned(a: array<int>, l1: int, u1: int, l2: int, u2: int)
{
	forall x, y :: 0 <= l1 <= x <= u1 < l2 <= y <= u2 < a.Length ==> a[x] <= a[y]
}

method BinarySearchWhile_Correct(a: array<int>, value: int) returns (index : int)
	requires 0 <= a.Length && sorted(a, 0, a.Length - 1)
	ensures (0 <= index ==> index < a.Length && a[index] == value) 
	ensures (index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value)
{
  var low : int := 0; 
  var high : int := a.Length; 
  var mid : int;

  while (low < high)
    invariant sorted(a, 0, a.Length - 1) 
    invariant 0 <= low <= high <= a.Length
    invariant 0 < low ==> a[0] != value 
    invariant forall i :: 0 < i < low ==> a[i] != value   
    invariant forall i :: high <= i < a.Length ==> a[i] != value
  {
    mid := (low + high) / 2;
    if (a[mid] < value) { low := mid + 1; }
    else if (value < a[mid]) { high := mid; }
    else { return mid; }
  }
  return -1;
}