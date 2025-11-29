predicate sorted_seq(a: seq<int>)
{
   forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i + 1]
}

predicate sorted_slice(a: array<int>, start: int, end: int)
   requires 0 <= start < a.Length
   requires start <= end <= a.Length
   reads a
{
   // forall i :: start <= i < end - 1 ==> a[i] <= a[i + 1]
   forall i, j :: start <= i <= j < end ==> a[i] <= a[j]
}

predicate merged(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  reads b
  requires start >= 0
  requires end <= b.Length
  requires start <= end

{
  assert forall xs : seq<int>, a,b : int :: 0 <= a < b < |xs| ==> xs[a..b+1] == xs[a..b] + [xs[b]];
  assert forall xs : seq<int> :: xs[0..|xs|] == xs;
  multiset(a1) + multiset(a2) == multiset(b[start..end])
}

// Assuming a1 and a2 are each sorted, merge a1 and a2 into b, starting at `start`
// and ending at `end`. You can assume there is the right amount of space between
// `start` and `end` (write this as an `requires`!).
method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
    modifies b

    requires end - start == |a1| + |a2|
    requires 0 <= start < end <= b.Length
    requires |a1| > 0
    requires |a2| > 0
    requires sorted_seq(a1)
    requires sorted_seq(a2)

    ensures sorted_slice(b, start, end)
{
    var i := 0;  // index in a1
    var j := 0;  // index in a2
    for k := start to end
        invariant 0 <= start <= k <= end <= b.Length
        invariant 0 <= i <= |a1|
        invariant 0 <= j <= |a2|
        invariant i + j == k - start
        invariant (forall x :: start <= x < k && i < |a1| ==> (b[x] <= a1[i]))
        invariant (forall x :: start <= x < k && j < |a2| ==> (b[x] <= a2[j]))
        invariant sorted_slice(b, start, k)
    {
        if i < |a1| && (j == |a2| || a1[i] < a2[j])
        {
            b[k] := a1[i];
            i := i + 1;
        }
        else
        {
            assert(0 <= j < |a2|);
            b[k] := a2[j];
            j := j + 1;
        }
        assert((0 < j && 0 < i) ==> (b[k] == a1[i - 1] || b[k] == a2[j - 1]));
    }
}

method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
    modifies b

    requires 0 == start && end == b.Length && b.Length == |a1| + |a2|
    requires |a1| > 0
    requires |a2| > 0
    requires sorted_seq(a1)
    requires sorted_seq(a2)

    ensures sorted_slice(b, start, end)
    ensures merged(a1, a2, 0, b.Length, b)
{
    var i := 0; 
    var j := 0; 
    for k := start to end
        invariant 0 <= start <= k <= end <= b.Length
        invariant 0 <= i <= |a1|
        invariant 0 <= j <= |a2|
        invariant i + j == k - start
        invariant (forall x :: start <= x < k && i < |a1| ==> (b[x] <= a1[i]))
        invariant (forall x :: start <= x < k && j < |a2| ==> (b[x] <= a2[j]))
        invariant sorted_slice(b, start, k)
        invariant merged(a1[..i], a2[..j], start, k, b)
    {
        if i < |a1| && (j == |a2| || a1[i] < a2[j])
        {
            b[k] := a1[i];
            i := i + 1;
        }
        else
        {
            assert(0 <= j < |a2|);
            b[k] := a2[j];
            j := j + 1;
        }
        assert((0 < j && 0 < i) ==> (b[k] == a1[i - 1] || b[k] == a2[j - 1]));
    }
    
}

// Part 3

// Split A[] into 2 runs, sort both runs into B[], merge both runs from B[] to A[]
// iBegin is inclusive; iEnd is exclusive (A[iEnd] is not in the set).
method splitMerge(a: array<int>, start: int, end: int)
    requires start >= 0

    decreases end - start
{
    if end - start <= 1 {
        return;
    }
    var mid := (start + end) / 2;
    assert(0 <= mid);
    assert(mid <= end);
    assert(start >= 0);
    splitMerge(a, start, mid);
    splitMerge(a, mid, end);
    // assert(sorted_seq(a[start..mid]));
    // assert(sorted_seq(a[mid..end]));
    b := new int[start-end];
    mergeSimple(a[start..mid], a[mid..end], start, end, b);
    a = (i requires 0 <= i < a.Length => b[i]);
}

predicate sorted_arr(a: array<int>)
   reads a
{
   forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] 
}

method mergeSort(a: array<int>) returns (b: array<int>)
    ensures sorted_arr(b)
{
    b := new int[a.Length];
    splitMerge(b, 0, a.Length); 
} 