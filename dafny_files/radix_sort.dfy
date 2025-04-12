// References:
// 1) https://stackoverflow.com/questions/63773783/understanding-dafny-code-termination-using-binary-search-as-an-example
// 2) "How would I find the minimum number and maximum number from an array in Dafny?"
// 3) "On line 12, what does this error 'Error: an update statement is allowed an effectful RHS only if there is just one RHS var min, max := ArrayMinNumber(arr), ArrayMaxNumber(arr);' mean?"
// 4) "How do I convert this python for loop code 'for i in range(n - 1, -1, -1):' into Dafny code?"
// 5) "How to prevent possible division by zero error when working with dafny variables and helper functions"
// 6) "What does the assertion might not hold mean in Dafny"

method Main() {
    var arr := new int[5];

    arr[0] := 12;
    arr[1] := 5;
    arr[2] := 18;
    arr[3] := 11;
    arr[4] := 5;

    var radix_sort_test := RadixSort(arr);
    print(radix_sort_test);
}

// Method with placeholder values commented, incase needed to start over

// method RadixSort(arr: array<int>) returns (new_arr: array<int>)
//     requires arr.Length > 0
// {
//     var max := ArrayMaxNumber(arr);
//     var num_digits := arr.Length;

//     for digit_place := 0 to num_digits {
//         arr := CountingSort(arr, digit_place);
//     }
    
//     new_arr := arr;
//     return new_arr;
// }

method RadixSort(arr: array<int>) returns (new_arr: array<int>)
    requires arr.Length > 0
{
    var max := ArrayMaxNumber(arr);
    var digit_place := 0;
    var sorted := arr;

    while Pow(10, digit_place) <= max
        invariant digit_place >= 0
        invariant sorted.Length == arr.Length
    {
        sorted := CountingSort(sorted, digit_place);
        digit_place := digit_place + 1;
    }
    new_arr := sorted;
    return new_arr;
}

// Method with placeholder values commented, incase needed to start over

// method CountingSort(arr: array<int>, digit_place : int) returns (new_arr: array<int>)
//     requires arr.Length > 0
// {
//     var n := arr.Length;
//     // var output := /* [0] * n */ ; // not done yet...
//     // var count := /* [0] * 10 */ ; // not done yet...

//     for i := 0 to arr.Length {
//         var digit := ; // (num // (10 ** digit_place)) % 10 not done yet...
//         /* count[digit] += 1 --> not done yet... */
//     }

//     for i := 1 to 10 {
//         /* count[i] += count[i - 1] not done yet... */
//     }

//     var i := n - 1;
//     while i >= 0
//     {
//         /* body code not done yet...
//         num = arr[i]
//         digit = (num // (10 ** digit_place)) % 10
//         output[count[digit] - 1] = num
//         count[digit] -= 1
//         */

//         i := i - 1;
//     }

//     new_arr := arr;
//     return new_arr;
// }

function Pow(base: int, exp: nat): int
    requires base > 0
    decreases exp
{
    if exp == 0 then 1 else base * Pow(base, exp - 1)
}

method CountingSort(arr: array<int>, digit_place : int) returns (new_arr: array<int>)
    requires arr.Length > 0
    requires digit_place > 0
    ensures new_arr.Length == arr.Length
{
    var n := arr.Length;
    var output := new int[n];
    var count := new int[10];

    var i := 0;
    while i < n
        invariant 0 <= i <= n
    {
        var num := arr[i];
        var pow := Pow(10, digit_place);
        assert pow > 0;
        var digit := (num / pow) % 10;
        assert 0 <= digit < 10;
        count[digit] := count[digit] + 1;
        i := i + 1;
    }

    i := 1;
    while i < 10
        invariant 1 <= i <= 10
    {
        count[i] := count[i] + count[i - 1];
        i := i + 1;
    }

    i := n - 1;
    while i >= 0
        invariant -1 <= i < n
    {
        var num := arr[i];
        var pow := Pow(10, digit_place);
        assert pow > 0;
        var digit := (num / pow) % 10;
        assert 0 <= digit < 10;
        count[digit] := count[digit] - 1;
        output[count[digit]] := num;
        i := i - 1;
    }

    new_arr := output;
    return new_arr;
}

method ArrayMaxNumber(arr: array<int>) returns (max_val : int)
    requires arr.Length > 0
{
    max_val := arr[0];

    var i: int := 1;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant max_val in arr[0..i]
    {
        if arr[i] > max_val {
            max_val := arr[i];
        }
        i := i + 1;
    }
    return max_val;
}
