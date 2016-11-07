
int x;

int main()
{
  x = 1;

  L:
  do {
    if (x) goto L; // main.0: -
  } while(0); // main.1: 1
}

