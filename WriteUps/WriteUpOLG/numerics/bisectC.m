function bisectC
beta=0.96; gam=3; J=60; K=J-1; ymax=2.98;
f=@(r) boundC(r,beta,gam,K) - 9/25/((16/25)*(r+2/25));
lo=0.05; hi=2; for it=1:200, m=(lo+hi)/2; if f(m)>0, hi=m; else lo=m; end, end
r=hi; R=1+r; x=0; for j=1:K+1, x=R*x+ymax; end
fprintf('bound (C) first beats demand at r = %.4f\n',r);
fprintf('  demand = %.4f, bound = %.4f, exact floor = %.4f\n', ...
  9/25/((16/25)*(r+2/25)), boundC(r,beta,gam,K), exactF(r,beta,gam,K));
fprintf('  reach(K+1) = %.4e  (crude closed form needed r=6.10, reach=6.0e50)\n',x);
% also: the ceiling endpoint and its demand
rl=-0.07; fprintf('  at r_lo=%.2f: ceiling %.2f vs demand %.2f\n', ...
  rl, 2.98/(1-(1+rl)), 9/25/((16/25)*(rl+2/25)));
end
function b=boundC(r,beta,gam,K)
R=1+r; Th=(beta*R)^(1/gam); q=Th/R; p=1/R;
v=zeros(K+2,1); u=v; for k=1:K+1, v(k+1)=q*(1+v(k)); u(k+1)=(1+u(k))/R; end
d=v-u; Glo=zeros(K+1,1); for k=0:K, Glo(k+1)=(1-q)*(Th^(k+1)-1)/(Th-1); end
b=(1-q)*sum(Glo(1:K).*d(2:K+1))/(K+1);
end
function b=exactF(r,beta,gam,K)
R=1+r; Th=(beta*R)^(1/gam); q=Th/R;
kap=zeros(K+2,1); kap(1)=1; for k=1:K+1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
v=zeros(K+2,1); u=v; for k=1:K+1, v(k+1)=q*(1+v(k)); u(k+1)=(1+u(k))/R; end
d=v-u; G=zeros(K+1,1); G(1)=1; for k=0:K-1, G(k+2)=1+G(k+1)*(1-kap(k+2))*R; end
b=sum(G(1:K).*kap(2:K+1).*d(2:K+1))/(K+1);
end
