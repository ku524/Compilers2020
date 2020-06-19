/* Simple Array & While */
{
  int[10] arr1;
  int[10] arr2;
  int n;
  int i;
  i = 0;
  n = 2;

  while (i < 10) {
    arr1[i] = n * i;
    i = i + 1;
  }  /* 0 2 4 8 16 32 64 128 256 512 */ 

  i = 0;

  while (i < 10) {
    arr2[i] = arr1[9 - i];
    i = i + 1;
  }  /* 512 256 128 64 32 16 8 4 2 0 */

  print (arr1[5] + arr2[3]);    /* 96 */
}