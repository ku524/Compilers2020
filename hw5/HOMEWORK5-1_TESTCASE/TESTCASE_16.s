/* FEATURE: print arr[i:j] (i included, j excluded) */
/* i and j are inputs, size(arr) = 10, arr[n] = n + 2 */
/* This program will print (i + 2) ~ (j + 1) */

{
  int i; int j; int idx;
  int[10] arr;

  read(i);
  read(j);
  idx = 0;

  arr[0] = 2;
  arr[1] = 3;
  arr[2] = 4;
  arr[3] = 5;
  arr[4] = 6;
  arr[5] = 7;
  arr[6] = 8;
  arr[7] = 9;
  arr[8] = 10;
  arr[9] = 11;

  while((idx < j) && (idx < 10)) {
    if(idx >= i){
      print(arr[idx]);
    }
    idx = idx + 1;
  }

}