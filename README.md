# CS-472-Dafny-Python-Sorting-Algos-Verification

Files Included:
1) python_files directory: bucket_sort.py and radix_sort.py
2) dafny_files directory: bucket_sort.dfy and radix_sort.dfy

Important Details (bucket_sort.dfy):
1) BucketSort method:
A method that takes an array of integer type and returns an integer value and requires that the length of the array be greater than 0, meaning that there has to be at least one element in the array itself. First it retrieves the number of buckets as being the length of the original array, minimum and maximum numbers from the ArrayMinNumber and ArrayMaxNumber helper functions. Then, it will loop through every element in the original array and sets the value of (num - min_val) / (max_val - min_val) * (num_buckets - 1) to an index integer variable and sets the bucket of variable index and assigns the num variable to that index. Finally, it will loop through every index in the buckets data structure and takes every element in the data structure and assigns it to a new array and returns that array.
2) CreateEmptyBuckets method:
A method that takes an integer and returns a sequence of a sequence list and requires that the integer is greater than or equal to 0. It first loops from 0 to the integer provided and sets each index of the list to a list and returns that sequence of a sequence list.
3) ArrayMaxNumber method: 
A method that takes an array of integer type and returns an integer value and requires that the length of the array be greater than 0, meaning that there has to be at least one element in the array itself. It checks if the current array index is greater than the current lowest integer value and if so, set the maximum value integer variable to that index until the last index of the array and return that maximum integer value variable.
4) ArrayMinNumber method:
A method that takes an array of integer type and returns an integer value and requires that the length of the array be greater than 0, meaning that there has to be at least one element in the array itself. It checks if the current array index is lower than the current lowest integer value and if so, set the minimum value integer variable to that index until the last index of the array and return that minimum integer value variable.

Important Details (radix_sort.dfy):
1) RadixSort method:
A method that takes an array of integer type and returns a new sorted array and requires that length of the array be greater than 0, meaning that there has to be at least one element in the array itself. It retrieves the max number from the original array using the ArrayMaxNumber helper function and also stores the length of the original array to another integer variable. It will then loop through the array and modify the original array by calling on the CountingSort helper function and after the loop, a new integer array is created and is set to the modified original array and returns that new array.
2) Pow function:
A function that takes an integer and natural number data type and returns an integer and requires the integer parameter to be greater than 0 and for the natural number parameter to be decreasing. It calculates the exponent by checking if the "exp" natural number parameter is 0, it returns 1 and otherwise to return the "base" integer parameter times Pow(base, exp-1). 
3) CountingSort method: 
A method that takes an array of integer type and a digit place int type and returns a new sorted array and requires that length of the array be greater than 0, meaning that there has to be at least one element in the array itself. It stores the length of the array into 3 seperate variables. Then, it loops through the original array and will make the buckets for each ones digit number from 0-9 for each number in the original array and then return the new array created.
4) ArrayMaxNumber method:
A method that takes an array of integer type and returns an integer value and requires that the length of the array be greater than 0, meaning that there has to be at least one element in the array itself. It checks if the current array index is greater than the current lowest integer value and if so, set the maximum value integer variable to that index until the last index of the array and return that maximum integer value variable.

Other features we would add if we had more time for the project:
1) Trying out new data types such as string and character types and sorting them and see if Dafny can verify that the programs also work with those data types rather than just integer data types alone.
2) Verify more complex algorthims rather than Radix and Bubble sort such as B+ trees and Dijkstra algorithm