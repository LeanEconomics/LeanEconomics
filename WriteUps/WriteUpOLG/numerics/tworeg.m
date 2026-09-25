% Two-regime estimate.  Consumption obeys, at every (b,z'), the PRIMITIVE two-sided bracket
%    L(z') = kap_k (m + Hrisk_k(z'))   <=  C(z')  <=  U(z') = min( kap_k (m + Harith_k(z')), m )
% with m = y(z') + R b.  The ceiling m is the constrained regime's IDENTITY read as a bound, and it
% is what the previous worst case threw away.  Maximise Var_w(M/C) jointly over the box (vertices),
% then over the box intersected with the slope constraints kap dy <= dC <= dy.
function tworeg
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=1;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
R1=1.04; q=(R1/1.06)^(1/gam); Th1=(beta*R1)^(1/gam);
kap=zeros(J,1); kap(1)=1;
for k=1:J-1, kap(k+1)=kap(k)*R1/(Th1+kap(k)*R1); end
Ha=zeros(nz,J); Hr=zeros(nz,J);
for k=1:J-1
  Ha(:,k+1)=(Pi*(y+Ha(:,k)))/R1;
  x=y+Hr(:,k); pm=zeros(nz,1);
  for z=1:nz, w=Pi(z,:)'; pm(z)=1/(w'*(1./x)); end
  Hr(:,k+1)=min(pm/R1,(1/kap(k+1)-1)*y);
end
c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
Vv=dec2bin(0:2^nz-1)-'0';
fprintf(' stage | allowance | Var true | box-only worst | box+slope worst | verdict\n');
for k=[J-1 40 20]
  allow=Th1/(q*(1-kap(k+1)*R1))-1; Vt=0; Wb=0; Ws=0;
  for z=1:nz
    b1=max(m1(:,z)-c1f{k+1}(:,z),0);
    for i=1:12:na
      b=b1(i); if b<=0, continue; end
      mm=y+R1*b;
      L=kap(k+1)*(mm+Hr(:,k+1));
      U=min(kap(k+1)*(mm+Ha(:,k+1)),mm);
      L=min(L,U);
      Cn=zeros(nz,1);
      for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b,'linear','extrap'); end
      w=Pi(z,:)'; M=1/(w'*(1./Cn)); Vt=max(Vt,w'*((M./Cn).^2)-1);
      dy=diff(y);
      for v=1:size(Vv,1)
        C=L+(U-L).*Vv(v,:)';
        Mv=1/(w'*(1./C)); Wb=max(Wb,w'*((Mv./C).^2)-1);
        d=diff(C);
        if all(d>=kap(k+1)*dy-1e-12) && all(d<=dy+1e-12)
          Ws=max(Ws,w'*((Mv./C).^2)-1);
        end
      end
    end
  end
  if Ws<=allow, vd='PASS'; else, vd='fail'; end
  fprintf(' %5d | %9.4f | %8.4f | %14.4f | %15.4f | %s\n',k,allow,Vt,Wb,Ws,vd);
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
