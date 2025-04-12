# This python file was from --> https://programiz.pro/resources/dsa-bucket-sort-complexity/

# This bucket sort Python code is used as a reference point for the "psuedocode"
# so we don't forget who bucket sort works and convert it to Dafny code

def bucket_sort(arr):
    """Sorts a list of numbers using the bucket sort algorithm."""
    
    if not arr:
        return arr

    max_val = max(arr)
    min_val = min(arr)
    num_buckets = len(arr)

    buckets = [[] for _ in range(num_buckets)]

    for num in arr:
        index = int((num - min_val) / (max_val - min_val) * (num_buckets - 1))
        buckets[index].append(num)

    sorted_arr = []
    for bucket in buckets:
        sorted_arr.extend(sorted(bucket))
    
    return sorted_arr