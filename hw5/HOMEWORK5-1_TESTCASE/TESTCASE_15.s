/* FEATURE: seek value in binary tree */
/* for input i, if (1 < i < 9), print 1, else print 0 */

{
  int n;
  int[8] arr;
  int i;
  int idx;
  int flag;
  

  n = 8;
  arr[0] = 5;
  arr[1] = 3;
  arr[2] = 7;
  arr[3] = 2;
  arr[4] = 4;
  arr[5] = 6;
  arr[6] = 8;
  flag = 0;
  idx = 1;

  read(i);

  while ((i > 0) && (idx < n) && (! flag)) {
    if (arr[idx - 1] == i) {
      flag = 1;
      idx = n;
    }
    else {
      if (arr[idx - 1] < i) {
        idx = (2 * idx) + 1;
      }
      else {
        idx = 2 * idx;
      }
    }
  }
  
  print (flag);

}
