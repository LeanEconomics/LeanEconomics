% The CE step WITH the propensity floor in it.  Under the failure hypothesis b2 < b1, the drop in
% next period's consumption is at least kap_k R1 (b1-b2) = kap_k R1 D (propensity floor), so
%   C2(z',b2) <= C1(z',b1) - kap_k R1 D + dr b2 + eps_k
%   => M2 <= M1 + A(dr b2 - kap_k R1 D + eps_k),  and with c_i = M_i / Thorn_i exactly (interior),
%   D [1 + qA kap_k R1 / Th1] <= (qA/Th1) eps_k + (q-1) c1 + (qA/Th1) dr b2 - dr a.
% Per-stage multiplier on the carried error:
%   m_k = (qA_k/Th1) / (1 + qA_k kap_k R1 / Th1)      -- CONTRACTS iff m_k <= 1.
function damp
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
r1=0.04; r2=0.06; R1=1+r1;
fprintf(' gam |    q    |      TRUE A                        |   PRIMITIVE BOUND A <= M/Cmin\n');
for gam=[1 1.5 2 2.5 3 5]
  q=(R1/(1+r2))^(1/gam); Th1=(beta*R1)^(1/gam);
  kap=zeros(J,1); kap(1)=1;
  for k=1:J-1, kap(k+1)=kap(k)*R1/(Th1+kap(k)*R1); end
  c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
  Ak=ones(J,1); Abk=ones(J,1);
  for k=1:J-1
    A=0; Ab=0;
    for z=1:nz
      b1=max(m1(:,z)-c1f{k+1}(:,z),0);
      for i=1:6:na
        if b1(i)<=0, continue; end
        Cn=zeros(nz,1);
        for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b1(i),'linear','extrap'); end
        w=Pi(z,:)'; M=(w'*(Cn.^(-gam)))^(-1/gam);
        A=max(A,w'*((Cn/M).^(-gam-1)));
        Ab=max(Ab,M/min(Cn));
      end
    end
    Ak(k+1)=max(A,1); Abk(k+1)=max(Ab,1);
  end
  mk=zeros(J,1); mb=zeros(J,1);
  for k=1:J-1
    qA=q*Ak(k+1);  mk(k+1)=(qA/Th1)/(1+qA*kap(k+1)*R1/Th1);
    qB=q*Abk(k+1); mb(k+1)=(qB/Th1)/(1+qB*kap(k+1)*R1/Th1);
  end
  mm=max(mk(2:J)); pp=prod(mk(2:J));
  mmb=max(mb(2:J)); ppb=prod(mb(2:J));
  fprintf(' %4.1f | %.5f | A %7.4f m %7.4f prod %8.2e | Abnd %7.3f m %7.4f prod %8.2e\n',...
          gam,q,max(Ak),mm,pp,max(Abk),mmb,ppb);
end
fprintf('\n m_k is largest at the newborn stage (kap smallest); the product over stages is what\n');
fprintf(' multiplies any carried error, and the terminal error is exactly zero.\n');
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
