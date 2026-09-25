% Near/far split of the gradient sum A = sum_z' pi (C/M)^(-g-1).
%   A <= max_{near}(C/M)^(-g-1) * P_near + max_{far}(C/M)^(-g-1) * P_far
% Contraction needs  A <= Th1 / (q (1 - kap_k R1))  -- binding at the newborn stage (kap smallest).
function nearfar
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
r1=0.04; r2=0.06; R1=1+r1;
fprintf(' gam | stage | allowance | A true | split d=1 | split d=2 | P_far(d=1) | best < allow?\n');
for gam=[1 1.5 2]
  q=(R1/(1+r2))^(1/gam); Th1=(beta*R1)^(1/gam);
  kap=zeros(J,1); kap(1)=1;
  for k=1:J-1, kap(k+1)=kap(k)*R1/(Th1+kap(k)*R1); end
  c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
  for k=[J-1 30 10]
    allow=Th1/(q*(1-kap(k+1)*R1));
    At=0; B1=0; B2=0; Pf1=0;
    for z=1:nz
      b1=max(m1(:,z)-c1f{k+1}(:,z),0);
      for i=1:6:na
        if b1(i)<=0, continue; end
        Cn=zeros(nz,1);
        for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b1(i),'linear','extrap'); end
        w=Pi(z,:)'; M=(w'*(Cn.^(-gam)))^(-1/gam); rt=(Cn/M).^(-gam-1);
        At=max(At,w'*rt);
        for d=1:2
          nearm=abs((1:nz)'-z)<=d; Pn=sum(w(nearm)); Pf=1-Pn;
          bn=max(rt(nearm)); if any(~nearm), bf=max(rt(~nearm)); else, bf=0; end
          v=bn*Pn+bf*Pf;
          if d==1, B1=max(B1,v); Pf1=max(Pf1,Pf); else, B2=max(B2,v); end
        end
      end
    end
    best=min(B1,B2);
    if best<=allow, vd='YES'; else, vd=' no'; end
    fprintf(' %4.1f | %5d | %9.4f | %6.4f | %9.3f | %9.3f | %10.2e |      %s\n',...
            gam,k,allow,At,B1,B2,Pf1,vd);
  end
end
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
