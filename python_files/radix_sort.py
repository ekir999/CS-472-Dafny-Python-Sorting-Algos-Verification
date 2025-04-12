# Used ChatGPT to generate the file

# This radix sort Python code is used as a reference point for the "psuedocode"
# so we don't forget who bucket sort works and convert it to Dafny code

def radix_sort(arr):
    """Sorts a list of integers using radix sort."""

    max_value = max(arr)
    num_digits = len(str(max_value))

    for digit_place in range(num_digits):
        arr = counting_sort(arr, digit_place)
    return arr

def counting_sort(arr, digit_place):
    """Sorts a list of integers based on the digit at digit_place."""

    n = len(arr)
    output = [0] * n
    count = [0] * 10  # 10 possible digits (0-9)

    for num in arr:
        digit = (num // (10 ** digit_place)) % 10
        count[digit] += 1
    
    for i in range(1, 10):
        count[i] += count[i - 1]

    for i in range(n - 1, -1, -1):
        num = arr[i]
        digit = (num // (10 ** digit_place)) % 10
        output[count[digit] - 1] = num
        count[digit] -= 1

    return output