Rails.application.routes.draw do
  get 'admin/login'
  get 'admin/logout'
  get 'admin/mainpage'

  post 'admin/login' => 'admin#login'
  delete 'admin/logout' => 'admin#logout'
  get 'admin/logout' => 'admin#logout'
    


  get 'user/signup'
  get 'user/login'
  get 'user/mainpage'

  post 'user/signup' => 'user#signup'
  post 'user/login' => 'user#login'
  delete 'user/logout' => 'user#logout'
  get 'user/logout' => 'user#logout'
    

end
