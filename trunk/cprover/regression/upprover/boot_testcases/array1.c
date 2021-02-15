int main()
{
     int marks[10], i, n=10, sum = 0, average;
    
     for(i=0; i<n; ++i)
     {
          marks[i]=i;     
          sum += marks[i];
     }
     average = sum/n;

     assert(average<60);
}