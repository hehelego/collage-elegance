// Oh gosh, I'd rather formalize this in Coq.
// Dafny will never provide any assistant for you, after all it is never meant to be a proof _assistant_.

predicate sorted(a: seq<int>)
{
  forall j, k :: 0 <= j < k < |a| ==> a[j] <= a[k]
}
predicate merged(a1: seq<int>, a2: seq<int>, b: seq<int>)
{
  multiset(a1) + multiset(a2) == multiset(b)
}

// Assert that v is no greater than than any element in the suffix a[i..]
predicate leqSuf(a: seq<int>, i: int, v: int)
{
  forall j :: 0 <= j < |a| ==> (j >= i ==> v <= a[j])
}


// Though the correctness proof is simple and easy for human, it is extremely hard for automated reasoning tools ...
method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires end - start == |a1| + |a2|       // exactly the space needed to store the merged sequences
  requires 0 <= start < end <= b.Length     // sub-array range is valid
  requires sorted(a1) && sorted(a2)         // input sequences are sorted
  ensures sorted(b[start .. end])           // output is sorted
  ensures merged(a1, a2, b[start .. end])   // exactly those elements in a1 and a2
  // mutate only [start..end]
  ensures old(b[..start]) == b[..start]
  ensures old(b[end..]) == b[end..]
  ensures old(a1) == a1
  ensures old(a2) == a2
{
  var i, j, k, side := 0, 0, start, false;
  ghost var sa, sb := multiset{}, multiset{};

  while k < end
    decreases end - k
    invariant 0 <= i <= |a1| && 0 <= j <= |a2| && start <= k <= end
    invariant k - start == i + j
    invariant sorted(a1[i..]) && sorted(a2[j..]) && sorted(b[start .. k])
    invariant k > start ==> leqSuf(a1, i, b[k-1]) && leqSuf(a2, j, b[k-1])
    invariant k > start ==> (side && i > 0 && a1[i-1] == b[k-1]) || (!side && j > 0 && a2[j-1] == b[k-1])
    invariant sa == sb
    invariant sa == multiset(a1[..i]) + multiset(a2[..j])
    invariant sb == multiset(b[start..k])
    // mutating only [start..end]
    invariant old(b[..start]) == b[..start]
    invariant old(b[end..]) == b[end..]
  {
    if (i < |a1| && (j >= |a2| || a1[i] <= a2[j])){
      b[k], side := a1[i], true;
        sa := sa + multiset{a1[i]};
        sb := sb + multiset{b[k]};
        // Long...Long...Guiding
        // the underlying SMT solver must lack heuristics to guide reasoning the behavior of string and multiset,
        // especially when they are used together
        calc == {
          multiset(a1[..i+1]) + multiset(a2[..j]);
          { assert a1[..i+1] == a1[..i] + [a1[i]]; }
          multiset(a1[..i] + [a1[i]]) + multiset(a2[..j]);
          multiset(a1[..i]) + multiset{a1[i]} + multiset(a2[..j]);
        }
        i := i + 1;
        assert sa == multiset(a1[..i]) + multiset(a2[..j]);
    } else {
      b[k], side := a2[j], false;
        sa := sa + multiset{a2[j]};
        sb := sb + multiset{b[k]};
        calc == {
          multiset(a1[..i]) + multiset(a2[..j+1]);
          { assert a2[..j+1] == a2[..j] + [a2[j]]; }
          multiset(a1[..i]) + multiset(a2[..j] + [a2[j]]);
          multiset(a1[..i]) + multiset(a2[..j]) + multiset{a2[j]};
        }
        j := j + 1;
        assert sa == multiset(a1[..i]) + multiset(a2[..j]);

    }
    k := k+1;
  }
  calc == {
    sa; sb;
    multiset(a1[..i]) + multiset(a2[..j]);
    { assert a1[..i] == a1 && a2[..j] == a2; }
    multiset(a1[..]) + multiset(a2[..]);
  }
}

function min(a: int, b: int) : int { if a < b then a else b }

// sort the array a using auxiliary array, b.
method msort(b: array<int>, begin: int, end: int, a: array<int>)
  modifies a, b
  decreases end - begin
  requires 0 <= begin <= end <= a.Length == b.Length
  requires a[begin..end] == b[begin..end]
  ensures sorted(a[begin..end])
  ensures multiset(old(b[begin..end])) == multiset(old(a[begin..end])) == multiset(a[begin..end]) == multiset(b[begin..end])
  // operates on [begin..end]
  ensures old(b[..begin])==b[..begin] && old(a[..begin])==a[..begin]
  ensures old(b[end..])==b[end..] && old(a[end..])==a[end..]
{
  if (end - begin <= 1) { return; }
  var mid := (begin + end) / 2;

  ghost var oa, ob := a[..], b[..];

  // for precondition
  calc == {
    a[begin..mid];
    a[begin..end][..mid-begin];
    b[begin..end][..mid-begin];
    b[begin..mid];
  }
  msort(a, begin, mid, b);
  calc == {
    multiset(a[begin..mid]);
    multiset(b[begin..mid]);
    multiset(oa[begin..mid]);
    multiset(ob[begin..mid]);
  }
  calc == {
    multiset(a[begin..end]);
    {
      assert a[begin..end] == a[begin..mid] + a[mid..end];
    }
    multiset(a[begin..mid] + a[mid..end]);
    multiset(a[begin..mid]) + multiset(a[mid..end]);
    {
      assert multiset(a[begin..mid]) == multiset(b[begin..mid]);
      assert a[mid..end] == oa[mid..end];
      assert b[mid..end] == ob[mid..end];
      assert a[mid..end] == b[mid..end];
    }
    multiset(b[begin..mid]) + multiset(b[mid..end]);
  }

  // for precondition
  calc == {
    a[mid..end];
    a[begin..end][mid-begin..];
    old(a[begin..end])[mid-begin..];
    old(b[begin..end][mid-begin..]);
    old(b[mid..end]);
    b[mid..end];
  }
  msort(a, mid, end, b);
  calc == {
    multiset(a[mid..end]);
    multiset(b[mid..end]);
    multiset(old(b[mid..end]));
    multiset(old(a[mid..end]));
  }

  assert sorted(b[begin..mid]) && sorted(b[mid..end]);

  calc == {
    multiset(b[begin..end]);
    { assert b[begin..end] == b[begin..mid] + b[mid..end]; }
    multiset(b[begin..mid] + b[mid..end]);
    multiset(b[begin..mid]) + multiset(b[mid..end]);
    multiset(old(a[begin..mid])) + multiset(old(a[mid..end]));
    { assert old(a[begin..mid]) + old(a[mid..end]) == old(a[begin..end]); }
    multiset(old(a[begin..end]));
    multiset(old(b[begin..end]));
    multiset(old(a[begin..end]));
  }
  mergeSimple(b[begin..mid], b[mid..end], begin, end, a);
  // assert merged(b[begin..mid], b[mid..end], a[begin..end]);
}

// exposed interface for the merge sort implementation
method sort(a: array<int>)
  modifies a
  ensures sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  ghost var copy, l := multiset(a[0..a.Length]), a.Length;
  var b := new int[a.Length];
  for i := 0 to a.Length 
    invariant b[..i] == a[..i] == old(a[..i])
    invariant a == old(a)
    invariant forall l, r :: 0<=l<=r<=a.Length ==> a[l..r] == old(a[l..r])
  {
    ghost var ai := a[i];
    b[i] := a[i];
  }

  calc == {
    multiset(old(a[0..l]));
    copy;
    { assert a[0..l] == old(a[0..l]); }
    multiset(a[0..l]);
    multiset(b[0..l]);
    { assert b[0..l] == b[..]; }
    multiset(b[..]);
  }
  msort(b, 0, a.Length, a);
  calc == {
    multiset(a[..]);
    { assert a[..] == a[0..l]; }
    multiset(a[0..l]);
    multiset(b[0..l]);
    copy;
    multiset(old(a[0..l]));
    {
      assert old(a[0..l]) == old(a[..]);
    }
    multiset(old(a[..]));
  }
}