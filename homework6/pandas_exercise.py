import pandas as pd

# Here you have to do some exercises to familiarize yourself with pandas.
# Especially some basic operations based on pd.Series and pd.DataFrame

# TODO: Create a Series called `ser`:
#   x1  1.0
#   x2  -1.0
#   x3  2.0
# Your code here
ser = pd.Series([1.0, -1.0, 2.0],index=['x1','x2','x3'])

# TODO: Create a DataFrame called `df`:
#        x0   x1   x2
#   s0 -1.1  0.8 -2.5
#   s1 -1.3 -1.0 -1.2
#   s2  1.7  1.8  2.1
#   s3  0.9  0.3  1.1

# Your code here
df = pd.DataFrame(
 [[-1.1,  0.8, -2.5],
  [-1.3, -1.0, -1.2],
  [-1.7,  1.8, -2.1],
  [-0.9,  0.3,  1.1],],
  index=['s0','s1','s2','s3'],
  columns=['x0','x1','x2']
)


# TODO: select `df` by column="x1":
print( df['x1'])

# TODO: select `df` by third row and first column:
print(df.iloc[2,0])

# TODO: change `df`'s column's name x0 to y0:
df = df.rename( columns={'x0':'y0'})

# TODO: select `df` where column's name start with x:
print( df[df.columns[df.columns.str.startswith('x')]])

# TODO: change `ser`'s index to [y0,x1,x2]:
ser.index = df.columns

# TODO: change `df` where column y0 multiply -1.5:
df['y0'] = df['y0'] * -1.5
# TODO: calculate `df` dot `ser`:
print(df.dot(ser))

# TODO: merge `ser` with the result of previous task:
df.append(ser, ignore_index=True)
