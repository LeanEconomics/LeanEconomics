% Closed forms:  q=Th/R, p=1/R, S_k=sum_{i<=k} q^i, kappa_k=1/S_k,
%   v_k=sum_{i=1..k} q^i, u_k=sum_{i=1..k} p^i, d=v-u,
%   G_0=1, G_{k+1}=1+G_k(1-kappa_{k+1})R,  f_K = ybar*sum_{k<K} G_k kappa_{k+1} d_{k+1}
% Check the closed forms, then compare candidate provable lower bounds on f_K.
function geom
beta=0.96; gam=3; J=60; K=J-1; ybar=1;
fprintf('check closed forms at r=0.10:\n');
r=0.10; R=1+r; Th=(beta*R)^(1/gam); q=Th/R;
kap=zeros(K+1,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
Sc=zeros(K+1,1); for k=0:K, Sc(k+1)=sum(q.^(0:k)); end
fprintf('  max |kappa_k - 1/S_k| = %.3e\n',max(abs(kap-1./Sc)));
fprintf('  kappa_59 = %.6f, 1-q = %.6f, gap/(1-q) = %.4f, q^60 = %.4e\n', ...
  kap(K+1),1-q,(kap(K+1)-(1-q))/(1-q),q^(K+1));
fprintf('\n   r    | demand  |   exact f_K/(K+1) | (A) crude | (B) G>=1 | (C) G geom | (D) tail m\n');
for r=[0.06 0.08 0.10 0.12 0.15 0.20 0.30 0.50]
  R=1+r; Th=(beta*R)^(1/gam); q=Th/R; p=1/R; dem=9/25/((16/25)*(r+2/25));
  kap=zeros(K+2,1); kap(1)=1; for k=1:K+1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  v=zeros(K+2,1); u=v; for k=1:K+1, v(k+1)=q*(1+v(k)); u(k+1)=(1+u(k))/R; end
  d=v-u;
  G=zeros(K+1,1); G(1)=1; for k=0:K-1, G(k+2)=1+G(k+1)*(1-kap(k+2))*R; end
  inc=zeros(K,1); for k=0:K-1, inc(k+1)=G(k+1)*kap(k+2)*d(k+2)*ybar; end
  fex=sum(inc)/(K+1);
  A=(K/(K+1))*ybar*(1-q)*(Th-1)/R;
  B=(1-q)*sum(d(2:K+1))*ybar/(K+1);
  Glo=zeros(K+1,1); for k=0:K, Glo(k+1)=(1-q)*(Th^(k+1)-1)/(Th-1); end
  C=(1-q)*sum(Glo(1:K).*d(2:K+1))*ybar/(K+1);
  % (D) tail: for k>=m use G>=G_m^lower, kappa>=1-q, d>=d_{m+1}; best m
  best=0;
  for m=0:K-1
    val=(K-m)*Glo(m+1)*(1-q)*d(m+2)*ybar/(K+1);
    best=max(best,val);
  end
  fprintf(' %+.3f | %7.4f | %17.4f | %9.4f | %8.4f | %10.4f | %8.4f\n',r,dem,fex,A,B,C,best);
end
end
