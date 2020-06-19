/* Simple Application of Sieve of Eratosthenes */
{
  int[301] arr;
  int[301] prime;
  int[20] ni;
  int[20] point;
  int[20] sum;
  int cnt;
  int i;
  int j;
  int t;
  int m;
  int temp;
  int flag;
  int min;

  cnt = 0;
  i = 2;

  while (i <= 300) {
    if (arr[i] == 0) {
      prime[cnt] = i;
      cnt = cnt + 1;
      j = i * 2;
      while (j <= 300) {
        arr[j] = 1;
        j = j + i;
      }
    }
    i = i + 1;
  }

  read (t); /* 2 */
  while (t > 0) {
    read (m); /* 2 */
              /* 3 */

    i = m;
    while (i > 0) {
      read (temp); /* 3 5 */
                   /* 3 5 7 */
      ni[m - i] = temp;
      point[m - i] = 0;
      sum[m - i] = 0;
      j = 0;
      while (j < temp) {
        sum[m - i] = sum[m - i] + prime[j];
        j = j + 1;
      }
      i = i - 1;
    }

    flag = 0;
    while (flag == 0) {
      min = 0;
      i = 1;
      flag = 1;

      while (i < m) {
        if (!(sum[i] == sum[i - 1]))
          flag = 0;
        if (sum[i] < sum[min])
          min = i;
        i = i + 1;
      }

      if (flag == 0) {
        sum[min] = sum[min] - prime[point[min]];
        sum[min] = sum[min] + prime[point[min] + ni[min]];
        point[min] = point[min] + 1;
      }
    }

    i = 0;
    while (i < m) {
      print (-ni[i]);
      j = 0;
      while (j < ni[i]) {
        print (prime[point[i] + j]);
        j = j + 1;
      }
      i = i + 1;
    }
    print (0);
    print (sum[0]);
    t = t - 1;
  }
}