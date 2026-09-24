% The certainty-equivalent criterion c0 antitone in R is  W(R2) D(R1) <= W(R1) D(R2).
% Writing u_t, v_t for the normalised income and path-price weights at R1 and lam = R1/R2 < 1,
% that is   sum u_t lam^t  <=  sum v_t lam^{theta t},  theta = 1 - 1/gamma.
% Jensen on the concave x^theta gives the sufficient condition  U <= V^theta with
% U = sum u_t lam^t, V = sum v_t lam^t.  How much does that step cost?
function jensen
beta=0.96; J=60; rho=0.9; sigma=0.4; nz=7;
[Pi,y,~]=tauchen(rho,sigma,nz);
% CE income path seen from the top state: conditional means
yce=zeros(J,1); d=zeros(1,nz); d(nz)=1;
for t=1:J, yce(t)=d*y; d=d*Pi; end
yflat=ones(J,1);
fprintf('   path   |  r   | exact gamma* | Jensen gamma* | cost\n');
for r=[0.02 0.04 0.06]
  for p=1:2
    if p==1, yy=yflat; nm='flat  '; else yy=yce; nm='CE top'; end
    ge=bisect(@(g) exact(g,r,beta,J,yy),0.3,60);
    gj=bisect(@(g) jens(g,r,beta,J,yy),0.3,60);
    fprintf(' %s | %.2f | %12.3f | %13.3f | %.3f\n',nm,r,ge,gj,ge-gj);
  end
end
fprintf('\n at r=0.04, CE top state: exact criterion margin at gamma = 1,2,3,4,5\n');
for g=[1 2 3 4 5]
  fprintf('   gamma=%d : exact %+0.4e , Jensen %+0.4e\n',g,exact(g,0.04,beta,J,yce), ...
    jens(g,0.04,beta,J,yce));
end
end
function v=exact(gam,r,beta,J,y)
R1=1+r; R2=R1+1e-5; t=(0:J-1)';
W1=sum(y.*R1.^(-t)); W2=sum(y.*R2.^(-t));
D1=sum(beta.^(t/gam).*R1.^(t/gam-t)); D2=sum(beta.^(t/gam).*R2.^(t/gam-t));
v=W1*D2-W2*D1;          % >0 means c0 falls with R, i.e. Theorem 1 holds at a=0
end
function v=jens(gam,r,beta,J,y)
R1=1+r; R2=R1+1e-5; lam=R1/R2; th=1-1/gam; t=(0:J-1)';
u=y.*R1.^(-t); u=u/sum(u);
w=beta.^(t/gam).*R1.^(t/gam-t); w=w/sum(w);
U=sum(u.*lam.^t); V=sum(w.*lam.^t);
v=V^th-U;               % >0 means the Jensen-sufficient condition holds
end
function x=bisect(f,lo,hi)
if f(hi)>0, x=hi; return; end
if f(lo)<0, x=lo; return; end
for it=1:200, m=(lo+hi)/2; if f(m)>0, lo=m; else hi=m; end, end
x=lo;
end
function [Pi,y,nu]=tauchen(rho,sigma,nz)
sd=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd; hi=(xg(j)+h/2-rho*xg(i))/sd;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,Dg]=eig(Pi'); [~,k]=max(abs(diag(Dg))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
