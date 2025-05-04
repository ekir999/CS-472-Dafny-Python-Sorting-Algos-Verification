// Predicate to check if an array is sorted in non-decreasing order
predicate sorted(a: array<int>)
  requires a != null
  reads a
{
  forall i, j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

// Predicate to check if two sequences are permutations (same elements, possibly in different order)
predicate isPermutation(a: seq<int>, b: seq<int>) {
  multiset(a) == multiset(b)
}

// Flatten multiple sequences from buckets into a single sequence
function Flatten(buckets: array<seq<int>>): seq<int>
  requires buckets != null
  reads buckets
{
  FlattenFrom(buckets, 0)
}

// Helper function to recursively flatten buckets from a given index
function FlattenFrom(buckets: array<seq<int>>, i: int): seq<int>
  requires 0 <= i <= buckets.Length
  reads buckets
{
  if i == buckets.Length then []
  else buckets[i] + FlattenFrom(buckets, i + 1)
}

// Computes the bucket index for a given element
function BucketIndex(x: int, min: int, max: int, numBuckets: int): int
  requires min <= x <= max && numBuckets > 0
  ensures 0 <= BucketIndex(x, min, max, numBuckets) < numBuckets
{
  ((x - min) * numBuckets) / (max - min + 1)
}

// Finds the maximum number in the array
method ArrayMaxNumber(arr: array<int>) returns (max_val: int)
  requires arr.Length > 0
  ensures forall i :: 0 <= i < arr.Length ==> arr[i] <= max_val
  ensures exists i :: 0 <= i < arr.Length && arr[i] == max_val
{
  max_val := arr[0];
  var i := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> arr[j] <= max_val
    invariant exists j :: 0 <= j < i && arr[j] == max_val
    decreases arr.Length - i
  {
    if arr[i] > max_val {
      max_val := arr[i];
    }
    i := i + 1;
  }
}

// Finds the minimum number in the array
method ArrayMinNumber(arr: array<int>) returns (min_val: int)
  requires arr.Length > 0
  ensures forall i :: 0 <= i < arr.Length ==> min_val <= arr[i]
  ensures exists i :: 0 <= i < arr.Length && arr[i] == min_val
{
  min_val := arr[0];
  var i := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> min_val <= arr[j]
    invariant exists j :: 0 <= j < i && arr[j] == min_val
    decreases arr.Length - i
  {
    if arr[i] < min_val {
      min_val := arr[i];
    }
    i := i + 1;
  }
}

// Sorts an array using insertion sort (used for sorting individual buckets)
method InsertionSort(a: array<int>)
  requires a != null
  modifies a
  ensures sorted(a)
{
  var c := 0;
  while c < a.Length
    invariant 0 <= c <= a.Length
    invariant forall k, l :: 0 <= k < c <= l < a.Length ==> a[k] <= a[l]
    invariant forall k :: 0 < k < c ==> a[k-1] <= a[k]
    decreases a.Length - c
  {
    var m := c;
    var i := c + 1;
    // Find the index of the smallest element from c to end
    while i < a.Length
      invariant c + 1 <= i <= a.Length
      invariant c <= m < a.Length
      invariant forall j :: c <= j < i ==> a[m] <= a[j]
      decreases a.Length - i
    {
      if a[i] < a[m] {
        m := i;
      }
      i := i + 1;
    }
    // Swap to bring smallest element to position c
    a[m], a[c] := a[c], a[m];
    c := c + 1;
  }
}

// Distributes elements into buckets based on their values
method DistributeToBuckets(arr: array<int>, min: int, max: int, numBuckets: int) returns (buckets: array<seq<int>>)
  requires arr != null && numBuckets > 0 && min <= max
  ensures buckets != null && buckets.Length == numBuckets
  ensures isPermutation(arr[..], Flatten(buckets))
{
  buckets := new array<seq<int>>(numBuckets);
  var b := 0;
  // Initialize empty buckets
  while b < numBuckets
    invariant 0 <= b <= numBuckets
    decreases numBuckets - b
  {
    buckets[b] := [];
    b := b + 1;
  }

  var i := 0;
  // Place each element in its corresponding bucket
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> 0 <= BucketIndex(arr[j], min, max, numBuckets) < numBuckets
    invariant isPermutation(arr[..i], Flatten(buckets))
    decreases arr.Length - i
  {
    var idx := BucketIndex(arr[i], min, max, numBuckets);
    buckets[idx] := buckets[idx] + [arr[i]];
    i := i + 1;
  }
}

// Merges all buckets into the final sorted array
method MergeBuckets(buckets: array<seq<int>>, output: array<int>)
  requires buckets != null && output != null
  requires output.Length == |Flatten(buckets)|
  modifies output
  ensures sorted(output)
  ensures isPermutation(Flatten(buckets), output[..])
{
  var idx := 0;
  var b := 0;

  // Process each bucket
  while b < buckets.Length
    invariant 0 <= b <= buckets.Length
    invariant 0 <= idx <= output.Length
    invariant isPermutation(Flatten(buckets[..b]), output[..idx])
    decreases buckets.Length - b
  {
    // Copy bucket elements into a temp array for sorting
    var temp := new int[buckets[b].Length];
    var k := 0;
    while k < buckets[b].Length
      invariant 0 <= k <= temp.Length
      decreases temp.Length - k
    {
      temp[k] := buckets[b][k];
      k := k + 1;
    }

    InsertionSort(temp);

    // Add sorted bucket elements to final output array
    k := 0;
    while k < temp.Length
      invariant 0 <= k <= temp.Length && idx + k <= output.Length
      decreases temp.Length - k
    {
      output[idx] := temp[k];
      k := k + 1;
      idx := idx + 1;
    }
    b := b + 1;
  }
}

// Main BucketSort method
method BucketSort(arr: array<int>)
  requires arr != null && arr.Length >= 0
  modifies arr
  ensures sorted(arr)
  ensures isPermutation(old(arr[..]), arr[..])
{
  if arr.Length <= 1 {
    return; // Already sorted
  }

  var min := ArrayMinNumber(arr);
  var max := ArrayMaxNumber(arr);
  var numBuckets := if max == min then 1 else arr.Length;

  // Distribute elements to buckets and merge sorted buckets
  var buckets := DistributeToBuckets(arr, min, max, numBuckets);
  var sortedArr := new int[arr.Length];
  MergeBuckets(buckets, sortedArr);

  // Copy result back to original array
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    decreases arr.Length - i
  {
    arr[i] := sortedArr[i];
    i := i + 1;
  }
}
