int binary_search(int a[], int len, int key) {
    int low = 0;
    int high = len - 1;
    int mid;
    int midVal;

    while (low <= high) {
        mid = (low + high) / 2;
        midVal = a[mid];

        if (midVal < key) {
             low = mid + 1;
        }
        else if (midVal > key) {
             high = mid - 1;
        }
        else {
             return mid; // key found
        }
     }
     return -(low + 1);  // key not found.
}