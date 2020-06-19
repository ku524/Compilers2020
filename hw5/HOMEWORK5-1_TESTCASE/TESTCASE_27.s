/* Sort */
{
  int[10] arr;
  int n;
  int init;
  int k;
  int j;
  int i;

  n = 10;
  i = 0;

  arr[0] = -63;
  arr[1] = -17;
  arr[2] = 64;
  arr[3] = 24;
  arr[4] = 15;
  arr[5] = -7;
  arr[6] = -3;
  arr[7] = 8;
  arr[8] = 81;
  arr[9] = 11;

  do {
    j = 1;
    while(j < n - i) {
      k = j - 1;
      if (arr[k] > arr[j]) {
        init = arr[k];
        arr[k] = arr[j];
        arr[j] = init;
      }
      j = j + 1;
    }
    i = i + 1;
  }while(i < n);

  /* arr = -63 -17 -7 -3 8 11 15 24 64 81 */

  print (arr[7]);   /* 24 */
}
