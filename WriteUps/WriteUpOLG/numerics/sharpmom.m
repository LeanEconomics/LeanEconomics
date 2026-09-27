% The sharp moment bound in place of Lyapunov.  With u = (C/M)^(-g), E_w[u] = 1 exactly, and
%   A = E[u^p], p = 1+1/g.  For U >= 0 with mean 1:  E[U^p] <= (1+V)^(p-1) = (1+V)^(1/g)   (sharp),
% and with a lower bound lo on U the extremal is the two-point law {lo, xi}, xi = 1+V/(1-lo).
% Contraction needs A <= allow_k = Th1/(q(1-kap_k R1)).  So the variance may be as large as
%   V_lyap = allow^(2/p)-1   (old)   vs   V_new = allow^g - 1   (new, lo = 0).
function sharpmom
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
r1=0.04; r2=0.06; R1=1+r1;
fprintf(' gam | worst stage | allow-1 | A true | maxV   | lo min | Lyap  | new(lo=0) | new(lo) | Vlyap | Vnew | Vnew/maxV\n');
for gam=[1 1.5 2 2.5 3 5]
  q=(R1/(1+r2))^(1/gam); Th1=(beta*R1)^(1/gam); p=1+1/gam;
  kap=zeros(J,1); kap(1)=1;
  for k=1:J-1, kap(k+1)=kap(k)*R1/(Th1+kap(k)*R1); end
  c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
  worst=-inf;
  for k=1:J-1
    allow=Th1/(q*(1-kap(k+1)*R1));
    At=0; Vt=0; lo=inf;
    for z=1:nz
      b1=max(m1(:,z)-c1f{k+1}(:,z),0);
      for i=1:6:na
        if b1(i)<=0, continue; end
        Cn=zeros(nz,1);
        for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b1(i),'linear','extrap'); end
        w=Pi(z,:)'; M=(w'*(Cn.^(-gam)))^(-1/gam);
        u=(Cn/M).^(-gam);
        At=max(At,w'*(u.^p)); Vt=max(Vt,w'*(u.^2)-1); lo=min(lo,min(u));
      end
    end
    Lb=(1+Vt)^(p/2); Nb=(1+Vt)^(p-1);
    xi=1+Vt/(1-lo); wxi=(1-lo)/(xi-lo); Nlo=(1-wxi)*lo^p+wxi*xi^p;
    Vl=allow^(2/p)-1; Vn=allow^gam-1;
    score=Nb-allow;   % positive = new bound fails contraction at this stage
    if score>worst, worst=score; rec=[k allow-1 At Vt lo Lb Nb Nlo Vl Vn Vn/Vt]; end
  end
  fprintf(' %4.1f | %11d | %7.4f | %6.4f | %6.4f | %6.4f | %5.4f | %9.4f | %7.4f | %5.4f | %4.4f | %5.2fx\n',gam,rec);
end
fprintf('\n "worst stage" = stage where the new bound (lo=0) has least slack against the allowance.\n');
fprintf(' new(lo=0) <= 1+allow-1 at every stage  <=>  contraction from the sharp bound with only mean+variance.\n');
end
function c=egm(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  c{k+1}=min(cn,m);
end
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
