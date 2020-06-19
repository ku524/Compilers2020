/* Maximum Value of Input List */
{
  int[10] arr;
  int max;
  int i;
  int temp;

  i = 0;

  while (i < 10) {
    read (temp); /* 1 7 3 4 9 11 2 13 6 5 */
    arr[i] = temp;
    i = i + 1;
  }

  max = arr[0];
  i = 1;

  do {
    print (max); /* 1 7 7 7 9 11 11 13 13 */
    if (arr[i] > max)
      max = arr[i];
    i = i + 1;
  } while (i < 10);

  print (max); /* 13 */

}