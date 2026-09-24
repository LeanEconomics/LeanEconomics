% Sanity check on the Diamond algebra formalised in OLG/Diamond.lean.
%  (1) does the closed-form saving share solve the two-period problem?
%  (2) is the steady state unique, and does the saving rate really fall with R when gamma > 1?
function dcheck
beta=0.96^30; alpha=1/3; A=1; wmax=0;
fprintf('(1) closed form vs grid search for optimal saving\n');
fprintf('   gamma |   R   |  closed form |  grid argmax | gap\n');
for gam=[0.5 1 2 3 5]
  for R=[0.8 1.2 2.0]
    w=1; s=w/(1+beta^(-1/gam)*R^((gam-1)/gam));
    sg=linspace(1e-6,w-1e-6,400001);
    U=u(w-sg,gam)+beta*u(R*sg,gam); [~,i]=max(U);
    fprintf(' %7.1f | %5.2f | %12.6f | %12.6f | %.2e\n',gam,R,s,sg(i),abs(s-sg(i)));
    wmax=max(wmax,abs(s-sg(i)));
  end
end
fprintf('   worst gap %.2e (grid spacing %.2e)\n\n',wmax,sg(2)-sg(1));
fprintf('(2) steady state: number of positive crossings of k'' = k, and d(saveShare)/dR sign\n');
fprintf('   gamma | delta | crossings | k*      | saving rate at R=1.5 vs R=3\n');
for gam=[0.5 1 2 3 5 10]
  for delta=[1 0.5]
    kg=exp(linspace(log(1e-8),log(50),200000));
    R=1-delta+alpha*A*kg.^(alpha-1);
    sh=1./(1+beta^(-1/gam)*R.^((gam-1)/gam));
    kp=sh.*((1-alpha)*A*kg.^alpha);
    g=kp-kg; cr=sum(g(1:end-1).*g(2:end)<0);
    i=find(g(1:end-1).*g(2:end)<0,1); ks=kg(i);
    s1=1/(1+beta^(-1/gam)*1.5^((gam-1)/gam)); s2=1/(1+beta^(-1/gam)*3^((gam-1)/gam));
    fprintf(' %7.1f | %5.2f | %9d | %7.4f | %.4f -> %.4f (%s)\n', ...
      gam,delta,cr,ks,s1,s2,string(s2>s1));
  end
end
end
function v=u(c,g), if g==1, v=log(c); else v=c.^(1-g)/(1-g); end, end
