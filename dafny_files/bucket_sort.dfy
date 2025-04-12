// References and ChatGPT Prompts used:
// 1) https://stackoverflow.com/questions/63773783/understanding-dafny-code-termination-using-binary-search-as-an-example
// 2) "How would I find the minimum number and maximum number from an array in Dafny?"
// 3) "On line 12, what does this error 'Error: an update statement is allowed an effectful RHS only if there is just one RHS var min, max := ArrayMinNumber(arr), ArrayMaxNumber(arr);' mean?"
// 4) "How do I do convert this Python code "num_buckets = len(arr) buckets = [[] for _ in range(num_buckets)]" into Dafny code?"
// 5) "How do I resolve the errors of "possible division by zero" and "LHS of array assignment must denote an array element (found seq<seq<int>>) RHS (of type int) not assignable to LHS (of type seq<int>)" within my program?"
// 6) "How do I loop through each element in the array rather than the index of the arrays in Dafny?"
// 7) "How do I concatenate an empty list into a set<set<int>> in Dafny?"

method Main() {
    var arr := new int[5];
    
    //initialize the array with some values
    arr[0] := 12;
    arr[1] := 5;
    arr[2] := 18;
    arr[3] := 11;
    arr[4] := 5;

    var bucket_sort_test := BucketSort(arr);
    print(bucket_sort_test);
}

method BucketSort(arr: array<int>) returns (new_arr: array<int>)
    requires arr.Length > 0
    ensures new_arr.Length == arr.Length
    ensures multiset(new_arr[..]) == multiset(arr[..])
    ensures forall i, j :: 0 <= i < j < new_arr.Length ==> new_arr[i] <= new_arr[j]
{
    // find min and max values in the array
    var min := ArrayMinNumber(arr);
    var max := ArrayMaxNumber(arr);

    // initialize the number of buckets to the length of the array
    var num_buckets := arr.Length;

    // calculate the range of the array and prevent division by zero
    var range := if max - min == 0 then 1 else max - min;
    
    // Create a sequence of empty buckets, decided to not use the method CreateEmptyBuckets due to errors
    var buckets := new seq<int>[num_buckets];
    var i := 0;
    while i < num_buckets
        invariant 0 <= i <= num_buckets
    {
        buckets[i] := [];
        i := i + 1;
    }
    
    // Distribute array elements into appropriate buckets
    i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
    {
        var index := ((arr[i] - min) * (num_buckets - 1)) / range;
        buckets[index] := buckets[index] + [arr[i]];
        i := i + 1;
    }
    
    // Sort each bucket individually and concatenate the result
    var sorted := [];
    var total := 0;
    var b := 0;
    while b < num_buckets
        invariant 0 <= b <= num_buckets
        /*next two lines error:
         this loop invariant could not be proved on entry
         Related message: loop invariant violation */

        //invariant total <= arr.Length // uncomment this and only line 90 gets out of bounds but postcondition is not proved
        //invariant total > arr.Length // uncomment this line and it gets index out of bounds only on line 48 but postcondition is proved

        invariant |sorted| == total
        decreases num_buckets - b
    {
        var bucket := buckets[b];
        var sb := [];
        var j := 0;

        // Insertion sort within each bucket
        while j < |bucket|
            invariant 0 <= j <= |bucket|
            invariant |sb| == j
        {
            // Append at correct position
            var k := 0;
            while k < |sb| && bucket[j] > sb[k]
                invariant 0 <= k <= |sb|
            {
                k := k + 1;
            }
            sb := sb[..k] + [bucket[j]] + sb[k..];
            j := j + 1;
        }

        sorted := sorted + sb;
        total := total + |sb|;
        b := b + 1;
    }

    // Copy sorted result to a new array
    new_arr := new int[arr.Length];
    var m := 0;
    while m < arr.Length
        invariant 0 <= m <= arr.Length
    {
        new_arr[m] := sorted[m];
        m := m + 1;
    }

    return new_arr;
}

method CreateEmptyBuckets(n: int) returns (result: seq<seq<int>>)
    requires n >= 0
{
    result := [];

    var i := 0;
    while i < n
        invariant 0 <= i <= n
    {
        result := result + [[]];
        i := i + 1;
    }

    return result;
}

method ArrayMaxNumber(arr: array<int>) returns (max_val: int)
    requires arr.Length > 0
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] <= max_val
    ensures exists i :: 0 <= i < arr.Length && arr[i] == max_val
{
    max_val := arr[0];
    var i := 1;
    // Linear scan to find maximum
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> arr[j] <= max_val
        invariant exists j :: 0 <= j < i && arr[j] == max_val
    {
        if arr[i] > max_val {
            max_val := arr[i];
        }
        i := i + 1;
    }
    return max_val;
}

method ArrayMinNumber(arr: array<int>) returns (min_val: int)
    requires arr.Length > 0
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] >= min_val
    ensures exists i :: 0 <= i < arr.Length && arr[i] == min_val
{
    min_val := arr[0];
    var i := 1;
    // Linear scan to find minimum
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> arr[j] >= min_val
        invariant exists j :: 0 <= j < i && arr[j] == min_val
    {
        if arr[i] < min_val {
            min_val := arr[i];
        }
        i := i + 1;
    }
    return min_val;
}
