% Bounding Var_w(u), u = M/C, at gamma = 1.  Need <= 0.066 (truth 0.041).
%   E[u^2] = M^2 * sum_w 1/C^2 ; M <= HM(C_hi) ; C >= C_lo.  Two candidate floors for C:
%     (a) LowerSandwich  : kap_k (y(z') + R b + H_minEarnings)
%     (b) Incidence      : kap_k (y(z') + R b + Hrisk_k(z'))    [the proved constraint-incidence floor]
%   Ceiling for C: kap_k (y(z') + R b + Harith_k(z')).
function varbnd
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=1;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
R1=1.04; q=(R1/1.06)^(1/gam); Th1=(beta*R1)^(1/gam);
kap=zeros(J,1); kap(1)=1;
for k=1:J-1, kap(k+1)=kap(k)*R1/(Th1+kap(k)*R1); end
Ha=zeros(nz,J); Hr=zeros(nz,J); Hm=zeros(J,1);
for k=1:J-1
  Ha(:,k+1)=(Pi*(y+Ha(:,k)))/R1;
  x=y+Hr(:,k); pm=zeros(nz,1);
  for z=1:nz, w=Pi(z,:)'; pm(z)=1/(w'*(1./x)); end
  Hr(:,k+1)=min(pm/R1,(1/kap(k+1)-1)*y);
  Hm(k+1)=(min(y)+Hm(k))/R1;
end
c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
fprintf(' stage | allowance on Var | Var true | bound (a) LowerSandwich | bound (b) Incidence\n');
for k=[J-1 40 20]
  allow=Th1/(q*(1-kap(k+1)*R1))-1;
  Vt=0; Ba=0; Bb=0;
  for z=1:nz
    b1=max(m1(:,z)-c1f{k+1}(:,z),0);
    for i=1:6:na
      b=b1(i); if b<=0, continue; end
      Cn=zeros(nz,1);
      for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b,'linear','extrap'); end
      w=Pi(z,:)'; M=1/(w'*(1./Cn));
      Vt=max(Vt,w'*((M./Cn).^2)-1);
      Clo_a=kap(k+1)*(y+R1*b+Hm(k+1));
      Clo_b=kap(k+1)*(y+R1*b+Hr(:,k+1));
      Chi  =kap(k+1)*(y+R1*b+Ha(:,k+1));
      Mub=1/(w'*(1./Chi));                    % M <= HM(C_hi)
      Ba=max(Ba,Mub^2*(w'*(1./Clo_a.^2))-1);
      Bb=max(Bb,Mub^2*(w'*(1./Clo_b.^2))-1);
    end
  end
  fprintf(' %5d | %16.4f | %8.4f | %23.3f | %19.3f\n',k,allow,Vt,Ba,Bb);
end
fprintf('\n the bound needs to come in under the allowance; both use only kap, y, Pi, b and H.\n');
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
