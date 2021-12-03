#include <stdlib.h>
#include <stdio.h>

unsigned count_increasing(unsigned depths[], int n) {
  int i; unsigned count; unsigned last;
  count = 0;
  last = depths[0];
  i = 1;
  while(i < n) {
    if (last < depths[i]) {
      count++;
    }
    last = depths[i];
    i++;
  }
  return count;
}

unsigned sum(unsigned buf[], int n) {
  int i; unsigned count;
  i = 0;
  count = 0;
  while(i < n) {
    count += buf[i];
    i++;
  }
  return count;
}

// Precondition: n <= window_size
int count_increasing_windowed(unsigned *depths, int n, int window_size) {
  int count = 0;

  unsigned* buffer = malloc(sizeof(unsigned) * window_size);
  int head = 0;

  // First, let's populate the buffer.
  for(int i = 0; i < window_size; i++) {
    buffer[i] = depths[i];
  }

  int last = sum(buffer, window_size);

  for(int i = window_size; i < n; i++) {
    buffer[head] = depths[i];
    int window_sum = sum(buffer, window_size);
    if (last < window_sum) {
      count++;
    }
    head = (head + 1) % window_size;
    last = window_sum;
  }

  return count;
}

int main() {
  FILE* fp = fopen("day1_test.txt", "r");
  unsigned* depths = malloc(sizeof(int) * 2048);
  unsigned* head = depths;
  int count = 0;
  while(fscanf(fp, "%d", head) != EOF) {
    head++;
    count++;
  }

  printf("Part 1: %d\n", count_increasing(depths, count));
  printf("Part 2: %d\n", count_increasing_windowed(depths, count, 3));

  return 0;
}
