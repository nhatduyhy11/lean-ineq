Bài toán
Cho các số không âm 
a,b,c≥0 thỏa mãn 
a+b+c=3. Chứng minh rằng:

a 
2
 +1
a
​
 + 
b 
2
 +1
b
​
 + 
c 
2
 +1
c
​
 ≤ 
5
2
​
 (ab+bc+ca+ 
4
3
​
 )
Bước 1: Quy đồng mẫu số và chuyển về biến 
p,q,r
Đặt:

p=a+b+c=3

q=ab+bc+ca

r=abc

Vì 
a,b,c≥0 và 
p=3, ta có các miền giá trị cơ bản:

0≤q≤ 
3
p 
2
 
​
 =3

r≥0

q 
2
 ≥3pr=9r⟹9r≤q 
2
 

Biệt thức 
Δ=(a−b) 
2
 (b−c) 
2
 (c−a) 
2
 ≥0, khai triển theo biến đối xứng:

Δ=9q 
2
 −4q 
3
 +(54q−108)r−27r 
2
 ≥0
Mẫu số chung của vế trái là tích:

Π=(a 
2
 +1)(b 
2
 +1)(c 
2
 +1)>0(với mọi a,b,c∈R)
Quy đồng mẫu số cả hai vế và nhân với 
10:

10⋅[ 
5
2
​
 (q+ 
4
3
​
 )⋅Π− 
cyc
∑
​
 a(b 
2
 +1)(c 
2
 +1)]≥0
Khai triển đại số theo 
p=3,q,r (được định lý poly_id trong mã Lean xác thực):

F(q,r):=(4q+3)r 
2
 +(12−34q)r+q(4q 
2
 −5q+4)≥0
Như vậy, bài toán quy về việc chứng minh 
F(q,r)≥0 trên miền:

0≤q≤3,r≥0,Δ≥0
Bước 2: Chứng minh 
F(q,r)≥0 theo từng khoảng của 
q
Ta chia đoạn 
q∈[0,3] thành 3 trường hợp:

Trường hợp 1: 
0≤q≤ 
3
1
​
 
Xét từng hạng tử của đa thức 
F(q,r):

4q+3>0⟹(4q+3)r 
2
 ≥0

Với 
q≤ 
3
1
​
 , ta có 
12−34q≥12− 
3
34
​
 = 
3
2
​
 >0⟹(12−34q)r≥0

Xét tam thức bậc hai:

4q 
2
 −5q+4=(2q− 
4
5
​
 ) 
2
 + 
16
39
​
 >0⟹q(4q 
2
 −5q+4)≥0
Tổng ba số hạng không âm nên:

F(q,r)≥0
Đẳng thức xảy ra khi và chỉ khi 
q=0 và 
r=0.

Trường hợp 2: 
q=3
Vì 
q=3= 
3
p 
2
 
​
  nên 
a=b=c=1⟹r=1.
Thay 
q=3 vào 
F(q,r):

F(3,r)=15r 
2
 −90r+75=15(r−1)(r−5)=15(1−r)(5−r)
Vì 
r≤( 
3
p
​
 ) 
3
 =1, ta có 
1−r≥0 và 
5−r>0.
Do đó 
F(3,r)≥0. Đẳng thức xảy ra khi 
r=1⟺a=b=c=1.

Trường hợp 3: 
3
1
​
 <q<3
Đặt:

s=3−q>0

Hệ số nhân 
c 
2
​
 =q(87−4q)>0 (vì 
0<q<3)

μ= 
54
4q 
2
 +69q−18
​
 >0 (vì với 
q> 
3
1
​
 , 
4q 
2
 +69q−18> 
9
4
​
 +23−18>0)

Ta có hằng đẳng thức phân tích tổng các bình phương (SOS Certificate):

2c 
2
​
 ⋅s⋅F(q,r)=2c 
2
​
 ⋅μ⋅Δ+[q((87−4q)r−(4q 
2
 +27q−42))] 
2
 + 
27
4
​
 s 
3
 q 
2
 (4q−9) 
2
 
Đánh giá từng số hạng ở vế phải:

2c 
2
​
 ⋅μ⋅Δ≥0 do 
c 
2
​
 >0,μ>0 và 
Δ≥0.

[q((87−4q)r−(4q 
2
 +27q−42))] 
2
 ≥0 (bình phương một số thực).

27
4
​
 s 
3
 q 
2
 (4q−9) 
2
 ≥0 (vì 
s=3−q>0 và có dạng bình phương).

Vì vế phải là tổng của 3 đại lượng không âm và 
2c 
2
​
 s>0, suy ra:

F(q,r)≥0
Bước 3: Phân loại các trường hợp dấu đẳng thức (
F(q,r)=0)
Dấu đẳng thức xảy ra khi và chỉ khi:

Từ TH1 (
q≤ 
3
1
​
 ):

q=0 v 
a
ˋ
  r=0
Vì 
a,b,c≥0 và 
ab+bc+ca=0, bắt buộc phải có ít nhất hai biến bằng 
0.
Kết hợp 
a+b+c=3⟹(a,b,c) là hoán vị của 
(3,0,0).

Từ TH2 (
q=3):

q=3 v 
a
ˋ
  r=1⟹a=b=c=1
Từ TH3 (
3
1
​
 <q<3):
Để tổng ba số hạng ở vế phải bằng 
0, mỗi số hạng phải đồng thời triệt tiêu:

Từ số hạng thứ ba:

27
4
​
 s 
3
 q 
2
 (4q−9) 
2
 =0⟺4q−9=0⟺q= 
4
9
​
 
Thay 
q= 
4
9
​
  vào số hạng thứ hai:

(87−4q)r−(4q 
2
 +27q−42)=0⟹78r−39=0⟺r= 
2
1
​
 
Khi 
q= 
4
9
​
  và 
r= 
2
1
​
 , ta có 
Δ=0, nghĩa là đa thức có nghiệm kép:

t 
3
 −3t 
2
 + 
4
9
​
 t− 
2
1
​
 =0⟺(t−2)(t− 
2
1
​
 ) 
2
 =0
Do đó, bộ ba 
(a,b,c) phải là hoán vị của 
(2, 
2
1
​
 , 
2
1
​
 ).

Kết luận
Bất đẳng thức được chứng minh hoàn tất. Đẳng thức xảy ra khi và chỉ khi:

(a,b,c)=(1,1,1)

(a,b,c) là hoán vị của 
(3,0,0)

(a,b,c) là hoán vị của 
(2, 
2
1
​
 , 
2
1
​
 )