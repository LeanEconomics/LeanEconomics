% A = sum_z' w (C/M)^(-g-1).  Put u = (C/M)^(-g); by the definition of M, E_w[u] = 1 EXACTLY.
% Then A = E[u^p] with p = 1 + 1/g in (1,2], and Lyapunov gives
%     A <= (E[u^2])^(p/2) = (1 + V)^((g+1)/(2g)),   V = Var_w(u),
% an identity at g = 1.  Contraction needs A <= Th1/(q(1-kap_k R1)).
function lyap
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
r1=0.04; r2=0.06; R1=1+r1;
fprintf(' gam | stage | allowance |  A true | max V  | Lyap bound | V allowed | slack on V\n');
for gam=[1 1.5 2 2.5 3]
  q=(R1/(1+r2))^(1/gam); Th1=(beta*R1)^(1/gam); p=1+1/gam;
  kap=zeros(J,1); kap(1)=1;
  for k=1:J-1, kap(k+1)=kap(k)*R1/(Th1+kap(k)*R1); end
  c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
  for k=[J-1 20]
    allow=Th1/(q*(1-kap(k+1)*R1));
    At=0; Vt=0;
    for z=1:nz
      b1=max(m1(:,z)-c1f{k+1}(:,z),0);
      for i=1:6:na
        if b1(i)<=0, continue; end
        Cn=zeros(nz,1);
        for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b1(i),'linear','extrap'); end
        w=Pi(z,:)'; M=(w'*(Cn.^(-gam)))^(-1/gam);
        u=(Cn/M).^(-gam);
        At=max(At,w'*(u.^p)); Vt=max(Vt,w'*(u.^2)-1);
      end
    end
    Lb=(1+Vt)^(p/2);
    Vall=allow^(2/p)-1;
    fprintf(' %4.1f | %5d | %9.4f | %7.4f | %6.4f | %10.4f | %9.4f | %8.2fx\n',...
            gam,k,allow,At,Vt,Lb,Vall,Vall/Vt);
  end
end
fprintf('\n slack on V is how loose a primitive variance bound may be and still contract.\n');
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
